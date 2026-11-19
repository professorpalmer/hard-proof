import Types
import Laws

open HP

namespace HPComplete

theorem laws_complete : ∀ f g : Impl, Passes f → Passes g → ∀ x : Input, Legal x → f x = g x := by
  intro f g hf hg x _
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  cases hr : x.refusal with
  | true => rw [f1 x hr, g1 x hr]
  | false =>
    cases hl : x.launch with
    | true => rw [f2 x hr hl, g2 x hr hl]
    | false =>
      cases hn : x.narrow with
      | true => rw [f3 x hr hl hn, g3 x hr hl hn]
      | false =>
        cases hb : x.broad with
        | true => rw [f4 x hr hl hn hb, g4 x hr hl hn hb]
        | false => rw [f5 x hr hl hn hb, g5 x hr hl hn hb]

end HPComplete
