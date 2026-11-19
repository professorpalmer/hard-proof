import Tbl
import TblLaws

open Tbl

namespace TblGap

/-- The first recovery rule. -/
def designA : Decide := fun c =>
  if c.b1 = true then
    if c.b0 = true then
      if c.b6 = true then
        if c.b10 = true then
          if c.b14 = true then
            if c.b2 = true then
              true
            else
              false
          else
            if c.b9 = true then
              if c.b8 = true then
                if c.b7 = true then
                  if c.b13 = true then
                    if c.b4 = true then
                      if c.b11 = true then
                        if c.b12 = true then
                          false
                        else
                          if c.b17 = true then
                            if c.b3 = true then
                              false
                            else
                              if c.b2 = true then
                                true
                              else
                                true
                          else
                            true
                      else
                        false
                    else
                      if c.b11 = true then
                        if c.b12 = true then
                          false
                        else
                          if c.b3 = true then
                            if c.b16 = true then
                              false
                            else
                              if c.b2 = true then
                                if c.b5 = true then
                                  false
                                else
                                  false
                              else
                                false
                          else
                            false
                      else
                        if c.b12 = true then
                          if c.b3 = true then
                            false
                          else
                            false
                        else
                          false
                  else
                    if c.b3 = true then
                      if c.b11 = true then
                        if c.b2 = true then
                          false
                        else
                          false
                      else
                        true
                    else
                      if c.b17 = true then
                        if c.b2 = true then
                          false
                        else
                          false
                      else
                        false
                else
                  if c.b16 = true then
                    true
                  else
                    if c.b11 = true then
                      if c.b12 = true then
                        if c.b13 = true then
                          if c.b17 = true then
                            if c.b5 = true then
                              false
                            else
                              true
                          else
                            false
                        else
                          false
                      else
                        if c.b13 = true then
                          if c.b17 = true then
                            if c.b15 = true then
                              false
                            else
                              if c.b4 = true then
                                true
                              else
                                true
                          else
                            false
                        else
                          true
                    else
                      if c.b15 = true then
                        false
                      else
                        if c.b5 = true then
                          if c.b12 = true then
                            false
                          else
                            true
                        else
                          if c.b4 = true then
                            true
                          else
                            false
              else
                if c.b2 = true then
                  if c.b5 = true then
                    if c.b7 = true then
                      false
                    else
                      true
                  else
                    if c.b7 = true then
                      if c.b16 = true then
                        if c.b17 = true then
                          true
                        else
                          true
                      else
                        if c.b3 = true then
                          if c.b17 = true then
                            if c.b11 = true then
                              true
                            else
                              true
                          else
                            false
                        else
                          true
                    else
                      false
                else
                  if c.b4 = true then
                    if c.b7 = true then
                      false
                    else
                      false
                  else
                    if c.b3 = true then
                      true
                    else
                      if c.b7 = true then
                        true
                      else
                        if c.b12 = true then
                          true
                        else
                          false
            else
              if c.b11 = true then
                if c.b16 = true then
                  if c.b3 = true then
                    true
                  else
                    if c.b12 = true then
                      if c.b7 = true then
                        false
                      else
                        false
                    else
                      false
                else
                  if c.b5 = true then
                    false
                  else
                    false
              else
                if c.b17 = true then
                  if c.b3 = true then
                    false
                  else
                    false
                else
                  if c.b16 = true then
                    false
                  else
                    false
        else
          false
      else
        if c.b7 = true then
          if c.b14 = true then
            if c.b15 = true then
              if c.b4 = true then
                false
              else
                true
            else
              true
          else
            if c.b4 = true then
              if c.b3 = true then
                if c.b5 = true then
                  false
                else
                  false
              else
                if c.b12 = true then
                  if c.b16 = true then
                    false
                  else
                    if c.b15 = true then
                      if c.b2 = true then
                        false
                      else
                        false
                    else
                      if c.b5 = true then
                        true
                      else
                        if c.b13 = true then
                          true
                        else
                          if c.b8 = true then
                            false
                          else
                            if c.b2 = true then
                              true
                            else
                              true
                else
                  if c.b15 = true then
                    if c.b13 = true then
                      false
                    else
                      if c.b9 = true then
                        true
                      else
                        false
                  else
                    if c.b10 = true then
                      if c.b2 = true then
                        if c.b13 = true then
                          true
                        else
                          false
                      else
                        false
                    else
                      true
            else
              if c.b8 = true then
                if c.b16 = true then
                  false
                else
                  false
              else
                if c.b10 = true then
                  if c.b15 = true then
                    if c.b11 = true then
                      if c.b2 = true then
                        true
                      else
                        true
                    else
                      if c.b5 = true then
                        if c.b12 = true then
                          if c.b16 = true then
                            false
                          else
                            true
                        else
                          if c.b3 = true then
                            if c.b9 = true then
                              if c.b16 = true then
                                false
                              else
                                false
                            else
                              false
                          else
                            false
                      else
                        if c.b3 = true then
                          if c.b13 = true then
                            if c.b16 = true then
                              false
                            else
                              false
                          else
                            false
                        else
                          false
                  else
                    if c.b13 = true then
                      false
                    else
                      true
                else
                  if c.b2 = true then
                    if c.b13 = true then
                      if c.b12 = true then
                        false
                      else
                        false
                    else
                      true
                  else
                    true
        else
          if c.b10 = true then
            if c.b12 = true then
              if c.b13 = true then
                false
              else
                true
            else
              if c.b8 = true then
                if c.b14 = true then
                  false
                else
                  if c.b9 = true then
                    true
                  else
                    true
              else
                if c.b16 = true then
                  true
                else
                  true
          else
            if c.b4 = true then
              if c.b14 = true then
                true
              else
                if c.b16 = true then
                  true
                else
                  if c.b8 = true then
                    true
                  else
                    if c.b5 = true then
                      false
                    else
                      false
            else
              if c.b16 = true then
                if c.b9 = true then
                  if c.b2 = true then
                    true
                  else
                    true
                else
                  if c.b14 = true then
                    if c.b13 = true then
                      if c.b3 = true then
                        false
                      else
                        false
                    else
                      true
                  else
                    if c.b2 = true then
                      if c.b5 = true then
                        true
                      else
                        if c.b15 = true then
                          if c.b11 = true then
                            false
                          else
                            false
                        else
                          if c.b8 = true then
                            true
                          else
                            true
                    else
                      if c.b8 = true then
                        false
                      else
                        if c.b11 = true then
                          if c.b3 = true then
                            false
                          else
                            true
                        else
                          false
              else
                if c.b2 = true then
                  false
                else
                  if c.b15 = true then
                    if c.b13 = true then
                      false
                    else
                      false
                  else
                    true
    else
      if c.b6 = true then
        if c.b10 = true then
          if c.b4 = true then
            if c.b7 = true then
              if c.b3 = true then
                true
              else
                false
            else
              if c.b16 = true then
                true
              else
                if c.b2 = true then
                  true
                else
                  if c.b13 = true then
                    false
                  else
                    false
          else
            if c.b16 = true then
              if c.b13 = true then
                if c.b7 = true then
                  if c.b3 = true then
                    false
                  else
                    false
                else
                  false
              else
                true
            else
              if c.b8 = true then
                false
              else
                false
        else
          if c.b12 = true then
            if c.b9 = true then
              if c.b15 = true then
                if c.b4 = true then
                  if c.b14 = true then
                    if c.b2 = true then
                      if c.b3 = true then
                        true
                      else
                        if c.b5 = true then
                          if c.b17 = true then
                            if c.b11 = true then
                              false
                            else
                              true
                          else
                            if c.b13 = true then
                              true
                            else
                              false
                        else
                          if c.b17 = true then
                            if c.b16 = true then
                              true
                            else
                              false
                          else
                            false
                    else
                      if c.b5 = true then
                        if c.b16 = true then
                          if c.b11 = true then
                            true
                          else
                            false
                        else
                          true
                      else
                        if c.b3 = true then
                          false
                        else
                          if c.b7 = true then
                            false
                          else
                            false
                  else
                    if c.b5 = true then
                      if c.b8 = true then
                        false
                      else
                        true
                    else
                      if c.b8 = true then
                        if c.b7 = true then
                          false
                        else
                          false
                      else
                        if c.b3 = true then
                          if c.b7 = true then
                            if c.b16 = true then
                              if c.b11 = true then
                                true
                              else
                                false
                            else
                              true
                          else
                            false
                        else
                          if c.b16 = true then
                            if c.b7 = true then
                              if c.b2 = true then
                                if c.b17 = true then
                                  if c.b11 = true then
                                    true
                                  else
                                    false
                                else
                                  if c.b13 = true then
                                    if c.b11 = true then
                                      false
                                    else
                                      true
                                  else
                                    false
                              else
                                if c.b11 = true then
                                  if c.b13 = true then
                                    false
                                  else
                                    if c.b17 = true then
                                      false
                                    else
                                      true
                                else
                                  if c.b13 = true then
                                    true
                                  else
                                    if c.b17 = true then
                                      true
                                    else
                                      true
                            else
                              if c.b11 = true then
                                if c.b13 = true then
                                  if c.b17 = true then
                                    false
                                  else
                                    true
                                else
                                  false
                              else
                                false
                          else
                            false
                else
                  true
              else
                if c.b8 = true then
                  if c.b11 = true then
                    if c.b3 = true then
                      if c.b7 = true then
                        true
                      else
                        if c.b4 = true then
                          true
                        else
                          true
                    else
                      if c.b7 = true then
                        if c.b17 = true then
                          false
                        else
                          false
                      else
                        if c.b4 = true then
                          true
                        else
                          if c.b13 = true then
                            true
                          else
                            false
                  else
                    if c.b16 = true then
                      true
                    else
                      if c.b5 = true then
                        if c.b4 = true then
                          false
                        else
                          true
                      else
                        if c.b2 = true then
                          true
                        else
                          false
                else
                  if c.b11 = true then
                    if c.b16 = true then
                      false
                    else
                      if c.b2 = true then
                        if c.b13 = true then
                          true
                        else
                          false
                      else
                        if c.b14 = true then
                          false
                        else
                          if c.b4 = true then
                            if c.b7 = true then
                              true
                            else
                              true
                          else
                            false
                  else
                    false
            else
              if c.b11 = true then
                if c.b7 = true then
                  if c.b2 = true then
                    true
                  else
                    false
                else
                  if c.b13 = true then
                    if c.b2 = true then
                      true
                    else
                      true
                  else
                    true
              else
                if c.b14 = true then
                  false
                else
                  if c.b15 = true then
                    if c.b8 = true then
                      if c.b16 = true then
                        true
                      else
                        true
                    else
                      if c.b3 = true then
                        if c.b13 = true then
                          false
                        else
                          false
                      else
                        if c.b13 = true then
                          if c.b7 = true then
                            false
                          else
                            true
                        else
                          true
                  else
                    if c.b13 = true then
                      false
                    else
                      true
          else
            if c.b17 = true then
              if c.b4 = true then
                if c.b2 = true then
                  false
                else
                  if c.b16 = true then
                    if c.b14 = true then
                      if c.b11 = true then
                        false
                      else
                        if c.b3 = true then
                          false
                        else
                          false
                    else
                      if c.b7 = true then
                        false
                      else
                        true
                  else
                    if c.b9 = true then
                      if c.b15 = true then
                        false
                      else
                        true
                    else
                      true
              else
                if c.b9 = true then
                  if c.b16 = true then
                    if c.b14 = true then
                      if c.b5 = true then
                        if c.b11 = true then
                          true
                        else
                          false
                      else
                        if c.b8 = true then
                          false
                        else
                          if c.b15 = true then
                            if c.b7 = true then
                              false
                            else
                              false
                          else
                            if c.b11 = true then
                              false
                            else
                              if c.b13 = true then
                                true
                              else
                                true
                    else
                      if c.b15 = true then
                        if c.b3 = true then
                          false
                        else
                          true
                      else
                        false
                  else
                    if c.b15 = true then
                      false
                    else
                      if c.b13 = true then
                        false
                      else
                        false
                else
                  false
            else
              if c.b15 = true then
                if c.b2 = true then
                  if c.b13 = true then
                    if c.b4 = true then
                      if c.b8 = true then
                        if c.b9 = true then
                          if c.b7 = true then
                            true
                          else
                            if c.b5 = true then
                              if c.b16 = true then
                                false
                              else
                                true
                            else
                              false
                        else
                          false
                      else
                        true
                    else
                      if c.b11 = true then
                        true
                      else
                        false
                  else
                    if c.b3 = true then
                      if c.b14 = true then
                        true
                      else
                        true
                    else
                      if c.b4 = true then
                        true
                      else
                        false
                else
                  if c.b13 = true then
                    if c.b4 = true then
                      if c.b8 = true then
                        if c.b11 = true then
                          true
                        else
                          false
                      else
                        if c.b3 = true then
                          true
                        else
                          false
                    else
                      false
                  else
                    true
              else
                if c.b14 = true then
                  if c.b7 = true then
                    false
                  else
                    false
                else
                  if c.b3 = true then
                    true
                  else
                    false
      else
        if c.b12 = true then
          if c.b7 = true then
            if c.b17 = true then
              if c.b5 = true then
                if c.b14 = true then
                  if c.b13 = true then
                    if c.b16 = true then
                      if c.b2 = true then
                        if c.b3 = true then
                          false
                        else
                          if c.b11 = true then
                            if c.b10 = true then
                              if c.b4 = true then
                                true
                              else
                                true
                            else
                              if c.b8 = true then
                                false
                              else
                                if c.b4 = true then
                                  if c.b15 = true then
                                    false
                                  else
                                    if c.b9 = true then
                                      true
                                    else
                                      true
                                else
                                  if c.b9 = true then
                                    true
                                  else
                                    true
                          else
                            if c.b15 = true then
                              if c.b4 = true then
                                if c.b8 = true then
                                  if c.b10 = true then
                                    false
                                  else
                                    true
                                else
                                  false
                              else
                                true
                            else
                              if c.b8 = true then
                                false
                              else
                                true
                      else
                        true
                    else
                      true
                  else
                    if c.b15 = true then
                      true
                    else
                      true
                else
                  if c.b3 = true then
                    if c.b4 = true then
                      false
                    else
                      true
                  else
                    if c.b10 = true then
                      if c.b9 = true then
                        true
                      else
                        true
                    else
                      if c.b2 = true then
                        false
                      else
                        true
              else
                if c.b15 = true then
                  if c.b10 = true then
                    if c.b13 = true then
                      if c.b4 = true then
                        false
                      else
                        true
                    else
                      if c.b16 = true then
                        true
                      else
                        true
                  else
                    if c.b2 = true then
                      if c.b4 = true then
                        if c.b13 = true then
                          if c.b11 = true then
                            true
                          else
                            false
                        else
                          if c.b14 = true then
                            if c.b16 = true then
                              true
                            else
                              false
                          else
                            false
                      else
                        if c.b14 = true then
                          true
                        else
                          if c.b8 = true then
                            true
                          else
                            false
                    else
                      if c.b8 = true then
                        if c.b16 = true then
                          true
                        else
                          true
                      else
                        true
                else
                  true
            else
              if c.b10 = true then
                if c.b3 = true then
                  if c.b4 = true then
                    if c.b13 = true then
                      true
                    else
                      if c.b8 = true then
                        true
                      else
                        true
                  else
                    false
                else
                  if c.b16 = true then
                    if c.b5 = true then
                      if c.b14 = true then
                        if c.b4 = true then
                          false
                        else
                          if c.b11 = true then
                            true
                          else
                            if c.b13 = true then
                              true
                            else
                              false
                      else
                        false
                    else
                      if c.b8 = true then
                        if c.b9 = true then
                          if c.b4 = true then
                            if c.b13 = true then
                              true
                            else
                              true
                          else
                            if c.b14 = true then
                              true
                            else
                              true
                        else
                          if c.b15 = true then
                            if c.b11 = true then
                              true
                            else
                              true
                          else
                            if c.b13 = true then
                              true
                            else
                              if c.b2 = true then
                                true
                              else
                                true
                      else
                        if c.b4 = true then
                          false
                        else
                          if c.b14 = true then
                            true
                          else
                            false
                  else
                    if c.b9 = true then
                      if c.b11 = true then
                        if c.b4 = true then
                          if c.b5 = true then
                            false
                          else
                            true
                        else
                          if c.b5 = true then
                            false
                          else
                            true
                      else
                        if c.b8 = true then
                          false
                        else
                          if c.b13 = true then
                            if c.b15 = true then
                              true
                            else
                              if c.b2 = true then
                                true
                              else
                                true
                          else
                            if c.b5 = true then
                              true
                            else
                              true
                    else
                      if c.b11 = true then
                        if c.b13 = true then
                          if c.b14 = true then
                            if c.b15 = true then
                              if c.b5 = true then
                                if c.b4 = true then
                                  if c.b8 = true then
                                    false
                                  else
                                    if c.b2 = true then
                                      true
                                    else
                                      false
                                else
                                  true
                              else
                                true
                            else
                              if c.b2 = true then
                                if c.b5 = true then
                                  true
                                else
                                  false
                              else
                                true
                          else
                            if c.b15 = true then
                              if c.b4 = true then
                                false
                              else
                                false
                            else
                              true
                        else
                          if c.b14 = true then
                            true
                          else
                            false
                      else
                        if c.b8 = true then
                          if c.b14 = true then
                            false
                          else
                            if c.b5 = true then
                              if c.b4 = true then
                                if c.b13 = true then
                                  if c.b15 = true then
                                    true
                                  else
                                    false
                                else
                                  if c.b15 = true then
                                    true
                                  else
                                    true
                              else
                                true
                            else
                              if c.b15 = true then
                                false
                              else
                                true
                        else
                          false
              else
                if c.b11 = true then
                  if c.b16 = true then
                    if c.b8 = true then
                      if c.b3 = true then
                        false
                      else
                        if c.b2 = true then
                          false
                        else
                          false
                    else
                      if c.b15 = true then
                        false
                      else
                        false
                  else
                    if c.b2 = true then
                      true
                    else
                      false
                else
                  if c.b2 = true then
                    true
                  else
                    if c.b9 = true then
                      if c.b15 = true then
                        if c.b13 = true then
                          if c.b5 = true then
                            false
                          else
                            false
                        else
                          if c.b8 = true then
                            if c.b16 = true then
                              false
                            else
                              if c.b14 = true then
                                if c.b3 = true then
                                  false
                                else
                                  true
                              else
                                false
                          else
                            if c.b3 = true then
                              false
                            else
                              true
                      else
                        true
                    else
                      if c.b13 = true then
                        true
                      else
                        if c.b15 = true then
                          if c.b16 = true then
                            false
                          else
                            true
                        else
                          if c.b16 = true then
                            false
                          else
                            if c.b8 = true then
                              true
                            else
                              if c.b5 = true then
                                false
                              else
                                false
          else
            if c.b14 = true then
              if c.b10 = true then
                if c.b17 = true then
                  if c.b5 = true then
                    if c.b8 = true then
                      if c.b4 = true then
                        false
                      else
                        true
                    else
                      false
                  else
                    if c.b8 = true then
                      if c.b13 = true then
                        false
                      else
                        false
                    else
                      if c.b13 = true then
                        if c.b4 = true then
                          true
                        else
                          true
                      else
                        if c.b3 = true then
                          false
                        else
                          if c.b9 = true then
                            if c.b15 = true then
                              false
                            else
                              true
                          else
                            true
                else
                  true
              else
                if c.b3 = true then
                  false
                else
                  false
            else
              if c.b16 = true then
                if c.b8 = true then
                  if c.b2 = true then
                    if c.b17 = true then
                      if c.b11 = true then
                        if c.b10 = true then
                          if c.b13 = true then
                            if c.b4 = true then
                              true
                            else
                              false
                          else
                            if c.b5 = true then
                              false
                            else
                              if c.b9 = true then
                                false
                              else
                                true
                        else
                          if c.b13 = true then
                            true
                          else
                            if c.b5 = true then
                              if c.b9 = true then
                                if c.b15 = true then
                                  false
                                else
                                  true
                              else
                                if c.b3 = true then
                                  false
                                else
                                  true
                            else
                              false
                      else
                        if c.b13 = true then
                          if c.b10 = true then
                            if c.b3 = true then
                              if c.b9 = true then
                                true
                              else
                                if c.b5 = true then
                                  if c.b4 = true then
                                    true
                                  else
                                    false
                                else
                                  false
                            else
                              true
                          else
                            if c.b9 = true then
                              true
                            else
                              if c.b4 = true then
                                true
                              else
                                false
                        else
                          if c.b4 = true then
                            true
                          else
                            false
                    else
                      if c.b4 = true then
                        true
                      else
                        if c.b15 = true then
                          if c.b13 = true then
                            true
                          else
                            if c.b10 = true then
                              false
                            else
                              true
                        else
                          if c.b9 = true then
                            if c.b3 = true then
                              if c.b5 = true then
                                true
                              else
                                false
                            else
                              if c.b11 = true then
                                if c.b10 = true then
                                  false
                                else
                                  true
                              else
                                if c.b13 = true then
                                  true
                                else
                                  if c.b10 = true then
                                    false
                                  else
                                    true
                          else
                            false
                  else
                    if c.b9 = true then
                      if c.b10 = true then
                        true
                      else
                        if c.b17 = true then
                          true
                        else
                          if c.b11 = true then
                            false
                          else
                            false
                    else
                      if c.b17 = true then
                        if c.b15 = true then
                          if c.b4 = true then
                            if c.b13 = true then
                              true
                            else
                              if c.b11 = true then
                                false
                              else
                                true
                          else
                            true
                        else
                          if c.b5 = true then
                            if c.b3 = true then
                              true
                            else
                              true
                          else
                            if c.b10 = true then
                              true
                            else
                              if c.b3 = true then
                                if c.b11 = true then
                                  false
                                else
                                  true
                              else
                                true
                      else
                        if c.b5 = true then
                          true
                        else
                          true
                else
                  if c.b4 = true then
                    if c.b15 = true then
                      false
                    else
                      false
                  else
                    true
              else
                if c.b13 = true then
                  false
                else
                  false
        else
          if c.b16 = true then
            if c.b17 = true then
              if c.b4 = true then
                false
              else
                if c.b11 = true then
                  true
                else
                  false
            else
              if c.b15 = true then
                if c.b9 = true then
                  true
                else
                  if c.b4 = true then
                    false
                  else
                    if c.b7 = true then
                      false
                    else
                      true
              else
                false
          else
            if c.b4 = true then
              if c.b14 = true then
                if c.b11 = true then
                  true
                else
                  true
              else
                true
            else
              true
  else
    if c.b3 = true then
      if c.b11 = true then
        if c.b16 = true then
          if c.b5 = true then
            if c.b6 = true then
              false
            else
              if c.b7 = true then
                if c.b0 = true then
                  if c.b2 = true then
                    if c.b8 = true then
                      if c.b4 = true then
                        true
                      else
                        true
                    else
                      false
                  else
                    if c.b8 = true then
                      false
                    else
                      true
                else
                  true
              else
                true
          else
            if c.b17 = true then
              false
            else
              false
        else
          if c.b14 = true then
            if c.b5 = true then
              true
            else
              false
          else
            false
      else
        if c.b16 = true then
          true
        else
          if c.b14 = true then
            false
          else
            if c.b9 = true then
              if c.b15 = true then
                true
              else
                false
            else
              if c.b5 = true then
                if c.b13 = true then
                  true
                else
                  if c.b7 = true then
                    true
                  else
                    false
              else
                if c.b4 = true then
                  false
                else
                  if c.b13 = true then
                    false
                  else
                    true
    else
      if c.b7 = true then
        if c.b8 = true then
          true
        else
          false
      else
        if c.b16 = true then
          if c.b4 = true then
            if c.b9 = true then
              if c.b13 = true then
                if c.b12 = true then
                  false
                else
                  false
              else
                true
            else
              if c.b12 = true then
                if c.b11 = true then
                  true
                else
                  false
              else
                false
          else
            if c.b5 = true then
              if c.b15 = true then
                false
              else
                if c.b6 = true then
                  false
                else
                  if c.b12 = true then
                    false
                  else
                    false
            else
              if c.b13 = true then
                false
              else
                false
        else
          if c.b6 = true then
            if c.b9 = true then
              true
            else
              if c.b12 = true then
                if c.b14 = true then
                  true
                else
                  true
              else
                if c.b0 = true then
                  if c.b11 = true then
                    true
                  else
                    false
                else
                  true
          else
            if c.b13 = true then
              if c.b4 = true then
                false
              else
                if c.b17 = true then
                  false
                else
                  true
            else
              false

/-- The second recovery rule. -/
def designB : Decide := fun c =>
  if c.b0 = false ∧ c.b1 = true ∧ c.b2 = true ∧ c.b3 = false ∧ c.b4 = false ∧ c.b5 = true ∧ c.b6 = false ∧ c.b7 = true ∧ c.b8 = true ∧ c.b9 = false ∧ c.b10 = false ∧ c.b11 = false ∧ c.b12 = true ∧ c.b13 = true ∧ c.b14 = true ∧ c.b15 = false ∧ c.b16 = true ∧ c.b17 = true then true else designA c

/-- The case on which the two rules differ. -/
def input : Case := ⟨false, true, true, false, false, true, false, true, true, false, false, false, true, true, true, false, true, true⟩

/-- The first rule passes each law. -/
theorem a_passes : Passes designA := by
  unfold Passes Group0 Group1 Group2 Group3 Group4 Group5 Group6 Group7 Group8 Group9 Group10 Group11 Group12 Group13 Group14 Group15 Group16 Group17 Group18 Group19 Group20 Group21 Group22 Group23 Group24 Group25 Group26 Group27 Group28 Group29 Group30 Group31 Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 Law32 Law33 Law34 Law35 Law36 Law37 Law38 Law39 Law40 Law41 Law42 Law43 Law44 Law45 Law46 Law47 Law48 Law49 Law50 Law51 Law52 Law53 Law54 Law55 Law56 Law57 Law58 Law59 Law60 Law61 Law62 Law63 Law64 Law65 Law66 Law67 Law68 Law69 Law70 Law71 Law72 Law73 Law74 Law75 Law76 Law77 Law78 Law79 Law80 Law81 Law82 Law83 Law84 Law85 Law86 Law87 Law88 Law89 Law90 Law91 Law92 Law93 Law94 Law95 Law96 Law97 Law98 Law99 Law100 Law101 Law102 Law103 Law104 Law105 Law106 Law107 Law108 Law109 Law110 Law111 Law112 Law113 Law114 Law115 Law116 Law117 Law118 Law119 Law120 Law121 Law122 Law123 Law124 Law125 Law126 Law127 Law128 Law129 Law130 Law131 Law132 Law133 Law134 Law135 Law136 Law137 Law138 Law139 Law140 Law141 Law142 Law143 Law144 Law145 Law146 Law147 Law148 Law149 Law150 Law151 Law152 Law153 Law154 Law155 Law156 Law157 Law158 Law159 Law160 Law161 Law162 Law163 Law164 Law165 Law166 Law167 Law168 Law169 Law170 Law171 Law172 Law173 Law174 Law175 Law176 Law177 Law178 Law179 Law180 Law181 Law182 Law183 Law184 Law185 Law186 Law187 Law188 Law189 Law190 Law191 Law192 Law193 Law194 Law195 Law196 Law197 Law198 Law199 Law200 Law201 Law202 Law203 Law204 Law205 Law206 Law207 Law208 Law209 Law210 Law211 Law212 Law213 Law214 Law215 Law216 Law217 Law218 Law219 Law220 Law221 Law222 Law223 Law224 Law225 Law226 Law227 Law228 Law229 Law230 Law231 Law232 Law233 Law234 Law235 Law236 Law237 Law238 Law239 Law240 Law241 Law242 Law243 Law244 Law245 Law246 Law247 Law248 Law249 Law250 Law251 Law252 Law253 Law254 Law255 Law256 Law257 Law258 Law259 Law260 Law261 Law262 Law263 Law264 Law265 Law266 Law267 Law268 Law269 Law270 Law271 Law272 Law273 Law274 Law275 Law276 Law277 Law278 Law279 Law280 Law281 Law282 Law283 Law284 Law285 Law286 Law287 Law288 Law289 Law290 Law291 Law292 Law293 Law294 Law295 Law296 Law297 Law298 Law299 Law300 Law301 Law302 Law303 Law304 Law305 Law306 Law307 Law308 Law309 Law310 Law311 Law312 Law313 Law314 Law315 Law316 Law317 Law318 Law319 Law320 Law321 Law322 Law323 Law324 Law325 Law326 Law327 Law328 Law329 Law330 Law331 Law332 Law333 Law334 Law335 Law336 Law337 Law338 Law339 Law340 Law341 Law342 Law343 Law344 Law345 Law346 Law347 Law348 Law349 Law350 Law351 Law352 Law353 Law354 Law355 Law356 Law357 Law358 Law359 Law360 Law361 Law362 Law363 Law364 Law365 Law366 Law367 Law368 Law369 Law370 Law371 Law372 Law373 Law374 Law375 Law376 Law377 Law378 Law379 Law380 Law381 Law382 Law383 Law384 Law385 Law386 Law387 Law388 Law389 Law390 Law391 Law392 Law393 Law394 Law395 Law396 Law397 Law398 Law399 Law400 Law401 Law402 Law403 Law404 Law405 Law406 Law407 Law408 Law409 Law410 Law411 Law412 Law413 Law414 Law415 Law416 Law417 Law418 Law419 Law420 Law421 Law422 Law423 Law424 Law425 Law426 Law427 Law428 Law429 Law430 Law431 Law432 Law433 Law434 Law435 Law436 Law437 Law438 Law439 Law440 Law441 Law442 Law443 Law444 Law445 Law446 Law447 Law448 Law449 Law450 Law451 Law452 Law453 Law454 Law455 Law456 Law457 Law458 Law459 Law460 Law461 Law462 Law463 Law464 Law465 Law466 Law467 Law468 Law469 Law470 Law471 Law472 Law473 Law474 Law475 Law476 Law477 Law478 Law479 Law480 Law481 Law482 Law483 Law484 Law485 Law486 Law487 Law488 Law489 Law490 Law491 Law492 Law493 Law494 Law495 Law496 Law497 Law498 Law499 Law500 Law501 Law502 Law503 Law504 Law505 Law506 Law507 Law508 Law509 Law510
  repeat' apply And.intro
  all_goals (intro c; intros; simp [designA, *])

/-- The second rule passes each law. -/
theorem b_passes : Passes designB := by
  unfold Passes Group0 Group1 Group2 Group3 Group4 Group5 Group6 Group7 Group8 Group9 Group10 Group11 Group12 Group13 Group14 Group15 Group16 Group17 Group18 Group19 Group20 Group21 Group22 Group23 Group24 Group25 Group26 Group27 Group28 Group29 Group30 Group31 Law0 Law1 Law2 Law3 Law4 Law5 Law6 Law7 Law8 Law9 Law10 Law11 Law12 Law13 Law14 Law15 Law16 Law17 Law18 Law19 Law20 Law21 Law22 Law23 Law24 Law25 Law26 Law27 Law28 Law29 Law30 Law31 Law32 Law33 Law34 Law35 Law36 Law37 Law38 Law39 Law40 Law41 Law42 Law43 Law44 Law45 Law46 Law47 Law48 Law49 Law50 Law51 Law52 Law53 Law54 Law55 Law56 Law57 Law58 Law59 Law60 Law61 Law62 Law63 Law64 Law65 Law66 Law67 Law68 Law69 Law70 Law71 Law72 Law73 Law74 Law75 Law76 Law77 Law78 Law79 Law80 Law81 Law82 Law83 Law84 Law85 Law86 Law87 Law88 Law89 Law90 Law91 Law92 Law93 Law94 Law95 Law96 Law97 Law98 Law99 Law100 Law101 Law102 Law103 Law104 Law105 Law106 Law107 Law108 Law109 Law110 Law111 Law112 Law113 Law114 Law115 Law116 Law117 Law118 Law119 Law120 Law121 Law122 Law123 Law124 Law125 Law126 Law127 Law128 Law129 Law130 Law131 Law132 Law133 Law134 Law135 Law136 Law137 Law138 Law139 Law140 Law141 Law142 Law143 Law144 Law145 Law146 Law147 Law148 Law149 Law150 Law151 Law152 Law153 Law154 Law155 Law156 Law157 Law158 Law159 Law160 Law161 Law162 Law163 Law164 Law165 Law166 Law167 Law168 Law169 Law170 Law171 Law172 Law173 Law174 Law175 Law176 Law177 Law178 Law179 Law180 Law181 Law182 Law183 Law184 Law185 Law186 Law187 Law188 Law189 Law190 Law191 Law192 Law193 Law194 Law195 Law196 Law197 Law198 Law199 Law200 Law201 Law202 Law203 Law204 Law205 Law206 Law207 Law208 Law209 Law210 Law211 Law212 Law213 Law214 Law215 Law216 Law217 Law218 Law219 Law220 Law221 Law222 Law223 Law224 Law225 Law226 Law227 Law228 Law229 Law230 Law231 Law232 Law233 Law234 Law235 Law236 Law237 Law238 Law239 Law240 Law241 Law242 Law243 Law244 Law245 Law246 Law247 Law248 Law249 Law250 Law251 Law252 Law253 Law254 Law255 Law256 Law257 Law258 Law259 Law260 Law261 Law262 Law263 Law264 Law265 Law266 Law267 Law268 Law269 Law270 Law271 Law272 Law273 Law274 Law275 Law276 Law277 Law278 Law279 Law280 Law281 Law282 Law283 Law284 Law285 Law286 Law287 Law288 Law289 Law290 Law291 Law292 Law293 Law294 Law295 Law296 Law297 Law298 Law299 Law300 Law301 Law302 Law303 Law304 Law305 Law306 Law307 Law308 Law309 Law310 Law311 Law312 Law313 Law314 Law315 Law316 Law317 Law318 Law319 Law320 Law321 Law322 Law323 Law324 Law325 Law326 Law327 Law328 Law329 Law330 Law331 Law332 Law333 Law334 Law335 Law336 Law337 Law338 Law339 Law340 Law341 Law342 Law343 Law344 Law345 Law346 Law347 Law348 Law349 Law350 Law351 Law352 Law353 Law354 Law355 Law356 Law357 Law358 Law359 Law360 Law361 Law362 Law363 Law364 Law365 Law366 Law367 Law368 Law369 Law370 Law371 Law372 Law373 Law374 Law375 Law376 Law377 Law378 Law379 Law380 Law381 Law382 Law383 Law384 Law385 Law386 Law387 Law388 Law389 Law390 Law391 Law392 Law393 Law394 Law395 Law396 Law397 Law398 Law399 Law400 Law401 Law402 Law403 Law404 Law405 Law406 Law407 Law408 Law409 Law410 Law411 Law412 Law413 Law414 Law415 Law416 Law417 Law418 Law419 Law420 Law421 Law422 Law423 Law424 Law425 Law426 Law427 Law428 Law429 Law430 Law431 Law432 Law433 Law434 Law435 Law436 Law437 Law438 Law439 Law440 Law441 Law442 Law443 Law444 Law445 Law446 Law447 Law448 Law449 Law450 Law451 Law452 Law453 Law454 Law455 Law456 Law457 Law458 Law459 Law460 Law461 Law462 Law463 Law464 Law465 Law466 Law467 Law468 Law469 Law470 Law471 Law472 Law473 Law474 Law475 Law476 Law477 Law478 Law479 Law480 Law481 Law482 Law483 Law484 Law485 Law486 Law487 Law488 Law489 Law490 Law491 Law492 Law493 Law494 Law495 Law496 Law497 Law498 Law499 Law500 Law501 Law502 Law503 Law504 Law505 Law506 Law507 Law508 Law509 Law510
  repeat' apply And.intro
  all_goals (intro c; intros; simp [designA, designB, *])

/-- The two rules give different answers for the case. -/
theorem differ : designA input ≠ designB input := by decide

end TblGap
