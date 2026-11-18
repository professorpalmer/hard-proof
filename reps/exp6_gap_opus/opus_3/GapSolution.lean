import Laws
import Solution

open Laws

namespace Gap

/-- The first design is the lock in `Solution.lean`. -/
def designA : LockImpl := Exp.lock

/-- The second design is the same lock, but no release is ever accepted.
The owner keeps the lock until the owner exits. -/
def designB : LockImpl :=
  { Exp.lock with isOwner := fun _ _ => false }

/-- Process 5 starts, acquires, and releases. -/
def trace : List Event := [.spawn 5, .acquire 5, .release 5]

/-- The process that is inside for design B only. -/
def who : Proc := ⟨5, 0⟩

/-- A state of design B, seen as a state of the lock in `Solution.lean`. -/
def conv (s : State designB) : State Exp.lock := ⟨s.os, s.owner, s.cs⟩

theorem conv_step (s : State designB) (e : Event) (h : ∀ pid, e ≠ Event.release pid) :
    conv (step designB s e) = step Exp.lock (conv s) e := by
  cases e with
  | spawn pid =>
    cases hp : s.os.table pid <;> simp [step, conv, hp]
  | exit pid =>
    cases hp : s.os.table pid <;> simp [step, conv, hp]
  | acquire pid =>
    cases hp : s.os.table pid with
    | none => simp [step, conv, hp]
    | some t =>
      have hg : grants designB s = grants Exp.lock (conv s) := by
        cases ho : s.owner <;> simp [grants, conv, ho, designB, Exp.lock]
      have hg2 : grants Exp.lock (conv s) = grants Exp.lock ⟨s.os, s.owner, s.cs⟩ := rfl
      simp only [step, conv, hp]
      by_cases hc : grants designB s = true
      · have hc' : grants Exp.lock ⟨s.os, s.owner, s.cs⟩ = true := by
          rw [← hg2, ← hg]; exact hc
        simp only [hc, hc', ↓reduceIte]; rfl
      · have hc' : ¬ grants Exp.lock ⟨s.os, s.owner, s.cs⟩ = true := by
          rw [← hg2, ← hg]; exact hc
        simp only [hc, hc', ↓reduceIte, Bool.false_eq_true]
  | release pid => exact absurd rfl (h pid)

theorem step_release (s : State designB) (pid : Nat) :
    step designB s (Event.release pid) = s := by
  cases hp : s.os.table pid with
  | none => simp [step, hp]
  | some t =>
    cases ho : s.owner with
    | none => simp [step, hp, ho]
    | some r => simp [step, hp, ho, designB]; rfl

theorem inv_step (s : State designB) (e : Event) (h : Exp.Inv (conv s)) :
    Exp.Inv (conv (step designB s e)) := by
  by_cases hr : ∃ pid, e = Event.release pid
  · obtain ⟨pid, rfl⟩ := hr
    rw [step_release]; exact h
  · have h' : ∀ pid, e ≠ Event.release pid := fun pid he => hr ⟨pid, he⟩
    rw [conv_step s e h']
    exact Exp.inv_step _ e h

theorem inv_all (evs : List Event) : Exp.Inv (conv (replay designB evs)) :=
  Exp.replay_inv (fun s => Exp.Inv (conv s)) Exp.inv_init inv_step evs

theorem mutexB : Mutex designB := by
  intro evs p q hp hq
  have h := inv_all evs
  have h1 := (h.csOwner p hp).1
  have h2 := (h.csOwner q hq).1
  rw [h1] at h2
  exact Option.some.inj h2

theorem no_orphan_holdB : NoOrphanHold designB := by
  intro evs hg
  have h := inv_all evs
  cases ho : (replay designB evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(designB.alive (replay designB evs).os r)) = false := by
      simpa [grants, ho] using hg
    have halive : (replay designB evs).os.table r.pid = some r.tok := by
      simpa [designB, Exp.lock] using hg'
    exact ⟨r, h.ownerCs r ho halive, halive⟩

theorem holder_keeps_lockB : HolderKeepsLock designB := by
  intro evs e p hp hrel hexit
  rw [Exp.replay_snoc]
  by_cases hr : ∃ pid, e = Event.release pid
  · obtain ⟨pid, rfl⟩ := hr
    rw [step_release]; exact ⟨rfl, hp⟩
  · have h' : ∀ pid, e ≠ Event.release pid := fun pid he => hr ⟨pid, he⟩
    have hc := conv_step (replay designB evs) e h'
    obtain ⟨hown, hlive⟩ := (inv_all evs).csOwner p hp
    have k := Exp.keeps_step (conv (replay designB evs)) e p hp hown hlive hrel hexit
    rw [← hc] at k
    exact ⟨k.owner, k.cs⟩

theorem a_passes : Passes designA :=
  ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock, Exp.can_refuse, Exp.can_enter⟩

theorem b_passes : Passes designB :=
  ⟨mutexB, no_orphan_holdB, holder_keeps_lockB,
    ⟨[.spawn 5, .acquire 5], by decide⟩, ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩⟩

/-- After `trace`, `who` is in the critical section for design B only. -/
theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
