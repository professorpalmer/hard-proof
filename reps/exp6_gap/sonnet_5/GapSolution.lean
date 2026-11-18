import Laws
import Solution

open Laws

namespace Gap

def designA : LockImpl := Exp.lock

/-- Same as `Exp.lock`, but a release never clears the record. -/
def lockB : LockImpl where
  Rec := Proc
  record p := p
  alive os r := decide (os.table r.pid = some r.tok)
  isOwner _ _ := false

def designB : LockImpl := lockB

def trace : List Event := [.spawn 0, .acquire 0, .release 0]

def who : Proc := ⟨0, 0⟩

theorem a_passes : Passes designA :=
  ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock, Exp.can_refuse, Exp.can_enter⟩

open Exp (replay_inv proc_eq replay_snoc)

structure InvB (s : State lockB) : Prop where
  freshT : ∀ (pid t : Nat), s.os.table pid = some t → t < s.os.next
  freshO : ∀ r : Proc, s.owner = some r → r.tok < s.os.next
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p ∧ s.os.table p.pid = some p.tok
  ownerCs : ∀ r : Proc, s.owner = some r → s.os.table r.pid = some r.tok → s.cs r = true

theorem invB_init : InvB (init lockB) := by
  constructor <;> simp [init]

theorem invB_step (s : State lockB) (e : Event) (h : InvB s) : InvB (step lockB s e) := by
  obtain ⟨hT, hO, hC, hOC⟩ := h
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid with
    | some t0 => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | none =>
      simp only [step, hpid]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro q t hq
        show t < s.os.next + 1
        have hq' : (if q = pid then some s.os.next else s.os.table q) = some t := hq
        split at hq'
        · have : s.os.next = t := Option.some.inj hq'
          omega
        · have := hT q t hq'
          omega
      · intro r hr
        show r.tok < s.os.next + 1
        have := hO r hr
        omega
      · intro p hp
        obtain ⟨h1, h2⟩ := hC p hp
        refine ⟨h1, ?_⟩
        show (if p.pid = pid then some s.os.next else s.os.table p.pid) = some p.tok
        have hne : p.pid ≠ pid := by
          intro heq; rw [heq, hpid] at h2; cases h2
        simp only [hne, ↓reduceIte]; exact h2
      · intro r hr hlive
        have hlive' :
            (if r.pid = pid then some s.os.next else s.os.table r.pid) = some r.tok := hlive
        split at hlive'
        · have h1 : s.os.next = r.tok := Option.some.inj hlive'
          have h2 := hO r hr
          omega
        · exact hOC r hr hlive'
  | exit pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      simp only [step, hpid]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro q t hq
        show t < s.os.next
        have hq' : (if q = pid then none else s.os.table q) = some t := hq
        split at hq'
        · cases hq'
        · exact hT q t hq'
      · intro r hr; exact hO r hr
      · intro p hp
        have hp' : (if p = ⟨pid, t0⟩ then false else s.cs p) = true := hp
        split at hp'
        · cases hp'
        · rename_i hne
          obtain ⟨h1, h2⟩ := hC p hp'
          refine ⟨h1, ?_⟩
          show (if p.pid = pid then none else s.os.table p.pid) = some p.tok
          have hpne : p.pid ≠ pid := by
            intro heq
            apply hne
            rw [heq, hpid] at h2
            exact proc_eq heq (Option.some.inj h2).symm
          simp only [hpne, ↓reduceIte]; exact h2
      · intro r hr hlive
        have hlive' : (if r.pid = pid then none else s.os.table r.pid) = some r.tok := hlive
        split at hlive'
        · cases hlive'
        · rename_i hne
          have hcs := hOC r hr hlive'
          show (if r = ⟨pid, t0⟩ then false else s.cs r) = true
          have hrne : r ≠ ⟨pid, t0⟩ := by
            intro heq; apply hne; rw [heq]
          simp only [hrne, ↓reduceIte]; exact hcs
  | acquire pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      simp only [step, hpid]
      cases hg : grants lockB s with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩
      | true =>
        simp only [↓reduceIte]
        have hempty : ∀ p : Proc, s.cs p = false := by
          intro p
          cases hcs : s.cs p with
          | false => rfl
          | true =>
            obtain ⟨h1, h2⟩ := hC p hcs
            simp [grants, h1, h2, lockB] at hg
        refine ⟨hT, ?_, ?_, ?_⟩
        · intro r hr
          have hr' : (⟨pid, t0⟩ : Proc) = r := Option.some.inj hr
          show r.tok < s.os.next
          rw [← hr']; exact hT pid t0 hpid
        · intro p hp
          have hp' : (if p = ⟨pid, t0⟩ then true else s.cs p) = true := hp
          split at hp'
          · rename_i heq
            subst heq
            exact ⟨rfl, hpid⟩
          · rw [hempty p] at hp'; cases hp'
        · intro r hr _
          have hr' : (⟨pid, t0⟩ : Proc) = r := Option.some.inj hr
          show (if r = ⟨pid, t0⟩ then true else s.cs r) = true
          subst hr'; simp
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      cases ho : s.owner with
      | none => simp only [step, hpid, ho]; exact ⟨hT, hO, hC, hOC⟩
      | some r =>
        simp only [step, hpid, ho]
        have hio : lockB.isOwner r ⟨pid, t0⟩ = false := rfl
        simp only [hio, Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩

theorem invB_all (evs : List Event) : InvB (replay lockB evs) :=
  replay_inv InvB invB_init invB_step evs

structure KeepsB (s s' : State lockB) (p : Proc) : Prop where
  owner : s'.owner = s.owner
  cs : s'.cs p = true

theorem keepsB_step (s : State lockB) (e : Event) (p : Proc) (hp : s.cs p = true)
    (hown : s.owner = some p) (hlive : s.os.table p.pid = some p.tok)
    (hrel : e ≠ Event.release p.pid) (hexit : e ≠ Event.exit p.pid) :
    KeepsB s (step lockB s e) p := by
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid with
    | some t0 => simp only [step, hpid]; exact ⟨rfl, hp⟩
    | none => simp only [step, hpid]; exact ⟨rfl, hp⟩
  | exit pid =>
    have hne : pid ≠ p.pid := fun heq => hexit (by rw [heq])
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨rfl, hp⟩
    | some t0 =>
      simp only [step, hpid]
      have hpne : p ≠ ⟨pid, t0⟩ := fun heq => hne (by rw [heq])
      refine ⟨rfl, ?_⟩
      show (if p = ⟨pid, t0⟩ then false else s.cs p) = true
      simp only [hpne, ↓reduceIte]; exact hp
  | acquire pid =>
    have hg : grants lockB s = false := by simp [grants, hown, hlive, lockB]
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨rfl, hp⟩
    | some t0 =>
      simp only [step, hpid, hg, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, hp⟩
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨rfl, hp⟩
    | some t0 =>
      have hio : lockB.isOwner p ⟨pid, t0⟩ = false := rfl
      simp only [step, hpid, hown, hio, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, hp⟩

theorem b_passes : Passes designB := by
  show Passes lockB
  refine ⟨?_, ?_, ?_, ⟨[.spawn 5, .acquire 5], by decide⟩,
    ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩⟩
  · intro evs p q hp hq
    have h := invB_all evs
    have h1 := (h.csOwner p hp).1
    have h2 := (h.csOwner q hq).1
    rw [h1] at h2
    exact Option.some.inj h2
  · intro evs hg
    have h := invB_all evs
    cases ho : (replay lockB evs).owner with
    | none => simp [grants, ho] at hg
    | some r =>
      have hg' : (!(lockB.alive (replay lockB evs).os r)) = false := by
        simpa [grants, ho] using hg
      have halive : (replay lockB evs).os.table r.pid = some r.tok := by
        simpa [lockB] using hg'
      exact ⟨r, h.ownerCs r ho halive, halive⟩
  · intro evs e p hp hrel hexit
    rw [replay_snoc]
    obtain ⟨hown, hlive⟩ := (invB_all evs).csOwner p hp
    have k := keepsB_step (replay lockB evs) e p hp hown hlive hrel hexit
    exact ⟨k.owner, k.cs⟩

theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
