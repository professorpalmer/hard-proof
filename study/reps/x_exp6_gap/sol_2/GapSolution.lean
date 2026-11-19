import Laws
import Solution

open Laws

namespace Gap

def designA : LockImpl := Exp.lock

def designB : LockImpl where
  Rec := Proc
  record p := p
  alive os r := decide (os.table r.pid = some r.tok)
  isOwner _ _ := false

def trace : List Event := [.spawn 5, .acquire 5, .release 5]

def who : Proc := ⟨5, 0⟩

theorem a_passes : Passes designA := by
  exact ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock,
    Exp.can_refuse, Exp.can_enter⟩

abbrev toA (s : State designB) : State Exp.lock where
  os := s.os
  owner := s.owner
  cs := s.cs

abbrev InvB (s : State designB) : Prop := Exp.Inv (toA s)

theorem invB_init : InvB (init designB) := by
  constructor <;> simp [init, toA]

theorem grants_toA (s : State designB) :
    grants Exp.lock (toA s) = grants designB s := by
  cases howner : s.owner <;> simp [grants, howner, toA, designB, Exp.lock]

theorem invB_step (s : State designB) (e : Event) (h : InvB s) :
    InvB (step designB s e) := by
  rcases s with ⟨os, owner, cs⟩
  let s : State designB := ⟨os, owner, cs⟩
  change InvB s at h
  change InvB (step designB s e)
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid <;>
      simpa [step, hpid, toA] using Exp.inv_step (toA s) (.spawn pid) h
  | exit pid =>
    cases hpid : s.os.table pid <;>
      simpa [step, hpid, toA] using Exp.inv_step (toA s) (.exit pid) h
  | acquire pid =>
    cases hpid : s.os.table pid with
    | none =>
      simpa [step, hpid, toA] using Exp.inv_step (toA s) (.acquire pid) h
    | some t =>
      cases hg : grants designB s with
      | false =>
        simp only [step, hpid, hg, Bool.false_eq_true, ↓reduceIte]
        exact h
      | true =>
        have hgA : grants Exp.lock (toA s) = true := (grants_toA s).trans hg
        have hi := Exp.inv_step (toA s) (.acquire pid) h
        simp only [step, hpid, hgA, ↓reduceIte] at hi
        simp only [step, hpid, hg, ↓reduceIte]
        change Exp.Inv
          ({ os := s.os, owner := some ⟨pid, t⟩,
             cs := setCS s.cs ⟨pid, t⟩ true } : State Exp.lock)
        simpa [Exp.lock] using hi
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simpa [step, hpid, toA]
    | some t =>
      cases howner : s.owner <;> simpa [step, hpid, howner, designB, toA]

theorem invB_all (evs : List Event) : InvB (replay designB evs) :=
  Exp.replay_inv InvB invB_init invB_step evs

theorem mutexB : Mutex designB := by
  intro evs p q hp hq
  have h := invB_all evs
  have h1 := (h.csOwner p hp).1
  have h2 := (h.csOwner q hq).1
  rw [h1] at h2
  exact Option.some.inj h2

theorem noOrphanB : NoOrphanHold designB := by
  intro evs hg
  have h := invB_all evs
  cases ho : (replay designB evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(designB.alive (replay designB evs).os r)) = false := by
      simpa [grants, ho] using hg
    have halive : (replay designB evs).os.table r.pid = some r.tok := by
      simpa [designB] using hg'
    exact ⟨r, h.ownerCs r ho halive, halive⟩

theorem keepsB (s : State designB) (e : Event) (p : Proc)
    (hp : s.cs p = true) (hown : s.owner = some p)
    (hlive : s.os.table p.pid = some p.tok)
    (hrel : e ≠ Event.release p.pid) (hexit : e ≠ Event.exit p.pid) :
    (step designB s e).owner = s.owner ∧ (step designB s e).cs p = true := by
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid <;> simp [step, hpid, hp]
  | exit pid =>
    have hne : pid ≠ p.pid := fun heq => hexit (by rw [heq])
    cases hpid : s.os.table pid with
    | none => simp [step, hpid, hp]
    | some t =>
      have hpne : p ≠ ⟨pid, t⟩ := fun heq => hne (by rw [heq])
      simp [step, hpid, setCS, hpne, hp]
  | acquire pid =>
    have hg : grants designB s = false := by
      simp [grants, hown, hlive, designB]
    cases hpid : s.os.table pid <;> simp [step, hpid, hg, hp]
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simp [step, hpid, hp]
    | some t =>
      cases howner : s.owner <;> simp [step, hpid, howner, designB, hp]

theorem holderB : HolderKeepsLock designB := by
  intro evs e p hp hrel hexit
  rw [Exp.replay_snoc]
  obtain ⟨hown, hlive⟩ := (invB_all evs).csOwner p hp
  exact keepsB (replay designB evs) e p hp hown hlive hrel hexit

theorem b_passes : Passes designB := by
  exact ⟨mutexB, noOrphanB, holderB,
    ⟨[.spawn 5, .acquire 5], by decide⟩,
    ⟨[.spawn 5, .acquire 5], ⟨⟨5, 0⟩, by decide⟩⟩⟩

theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
