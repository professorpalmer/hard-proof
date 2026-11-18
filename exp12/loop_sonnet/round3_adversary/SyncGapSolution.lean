import Sync
import SyncLaws

open Sync

namespace SyncGap

def trim : List Entry → List Entry
  | a :: b :: t => if a = b then b :: t else a :: b :: t
  | l => l

theorem trim_mem (l : List Entry) (s : Entry) : s ∈ trim l ↔ s ∈ l := by
  match l with
  | [] => simp [trim]
  | [a] => simp [trim]
  | a :: b :: t =>
    simp only [trim]
    split
    · rename_i h; subst h; simp
    · exact Iff.rfl

theorem trim_sub (l : List Entry) : List.Sublist (trim l) l := by
  match l with
  | [] => simp [trim]
  | [a] => simp [trim]
  | a :: b :: t =>
    simp only [trim]
    split
    · exact List.sublist_cons_self _ _
    · exact List.Sublist.refl _

theorem trim_distinct {st : List Entry} (hd : DistinctIds st) : DistinctIds (trim st) := by
  intro s hs s' hs' h
  exact hd s ((trim_mem _ _).1 hs) s' ((trim_mem _ _).1 hs') h

/-- The first design. -/
def designA : SyncImpl := ref

/-- The second design. -/
def designB : SyncImpl := fun c st r => ref c (trim st) r

def config : Config := ⟨fun _ => false, false⟩
def starter : List Entry := [⟨1, 1, 1, false⟩, ⟨1, 1, 1, false⟩]
def registry : List Entry := []

theorem a_passes : Passes designA := ref_passes

theorem b_passes : Passes designB := by
  obtain ⟨k, ao, aa, ns, nd, ek, la, ord, ndu⟩ := ref_passes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c st r hd
    exact k c (trim st) r (trim_distinct hd)
  · intro c st r hd x hx hxr
    obtain ⟨s, hs, h⟩ := ao c (trim st) r (trim_distinct hd) x hx hxr
    exact ⟨s, (trim_mem _ _).1 hs, h⟩
  · intro c st r hd s hs ha
    exact aa c (trim st) r (trim_distinct hd) s ((trim_mem _ _).2 hs) ha
  · intro c st r hd x hx hxr
    exact ns c (trim st) r (trim_distinct hd) x hx hxr
  · intro c st r hd he s hs ha x hx hid
    exact nd c (trim st) r (trim_distinct hd) he s ((trim_mem _ _).2 hs) ha x hx hid
  · intro c st r hd he s hs ha hl x hx hid
    exact ek c (trim st) r (trim_distinct hd) he s ((trim_mem _ _).2 hs) ha hl x hx hid
  · intro c st r hd s hs ha hl x hx hid
    exact la c (trim st) r (trim_distinct hd) s ((trim_mem _ _).2 hs) ha hl x hx hid
  · intro c st r hd new h
    exact (ord c (trim st) r (trim_distinct hd) new h).trans ((trim_sub st).map _)
  · intro c st r hd i hi
    exact ndu c (trim st) r (trim_distinct hd) i hi

theorem starter_distinct : DistinctIds starter := by
  intro s hs s' hs' _
  simp [starter] at hs hs'
  subst hs; subst hs'; rfl

theorem differ : designA config starter registry ≠ designB config starter registry := by
  intro h
  have := congrArg List.length h
  simp [designA, designB, ref, trim, starter, registry, absent, hasId, hasIdentity] at this

end SyncGap
