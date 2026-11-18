import Laws
import Solution

open Laws

namespace Gap

open Exp (foldl_inv replay_inv proc_eq replay_snoc)

/-- Design B: the owner never releases when its pid is 7. Otherwise like `Exp.lock`. -/
def lock : LockImpl where
  Rec := Proc
  record p := p
  alive os r := decide (os.table r.pid = some r.tok)
  isOwner r p := decide (r = p) && decide (p.pid ≠ 7)

def designA : LockImpl := Exp.lock
def designB : LockImpl := lock
def trace : List Event := [.spawn 7, .acquire 7, .release 7]
def who : Proc := ⟨7, 0⟩

structure Inv (s : State lock) : Prop where
  freshT : ∀ (pid t : Nat), s.os.table pid = some t → t < s.os.next
  freshO : ∀ r : Proc, s.owner = some r → r.tok < s.os.next
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p ∧ s.os.table p.pid = some p.tok
  ownerCs : ∀ r : Proc, s.owner = some r → s.os.table r.pid = some r.tok → s.cs r = true

theorem inv_init : Inv (init lock) := by
  constructor <;> simp [init]

theorem inv_step (s : State lock) (e : Event) (h : Inv s) : Inv (step lock s e) := by
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
      cases hg : grants lock s with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩
      | true =>
        simp only [↓reduceIte]
        have hempty : ∀ p : Proc, s.cs p = false := by
          intro p
          cases hcs : s.cs p with
          | false => rfl
          | true =>
            obtain ⟨h1, h2⟩ := hC p hcs
            simp [grants, h1, h2, lock] at hg
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
        cases hio : lock.isOwner r ⟨pid, t0⟩ with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩
        | true =>
          simp only [↓reduceIte]
          have hrp : r = (⟨pid, t0⟩ : Proc) := by
            have h2 := hio
            simp [lock] at h2
            exact h2.1
          refine ⟨hT, ?_, ?_, ?_⟩
          · intro r' hr'
            have hr'' : (none : Option Proc) = some r' := hr'
            cases hr''
          · intro p hp
            have hp' : (if p = ⟨pid, t0⟩ then false else s.cs p) = true := hp
            split at hp'
            · cases hp'
            · rename_i hne
              obtain ⟨h1, _⟩ := hC p hp'
              rw [ho] at h1
              have hrp' : r = p := Option.some.inj h1
              exact absurd (hrp' ▸ hrp) hne
          · intro r' hr'
            have hr'' : (none : Option Proc) = some r' := hr'
            cases hr''

theorem inv_all (evs : List Event) : Inv (replay lock evs) :=
  replay_inv Inv inv_init inv_step evs

theorem mutex : Mutex lock := by
  intro evs p q hp hq
  have h := inv_all evs
  have h1 := (h.csOwner p hp).1
  have h2 := (h.csOwner q hq).1
  rw [h1] at h2
  exact Option.some.inj h2

theorem no_orphan_hold : NoOrphanHold lock := by
  intro evs hg
  have h := inv_all evs
  cases ho : (replay lock evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(lock.alive (replay lock evs).os r)) = false := by
      simpa [grants, ho] using hg
    have halive : (replay lock evs).os.table r.pid = some r.tok := by
      simpa [lock] using hg'
    exact ⟨r, h.ownerCs r ho halive, halive⟩

theorem can_refuse : CanRefuse lock := ⟨[.spawn 5, .acquire 5], by decide⟩

theorem can_enter : CanEnter lock := ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩

structure Keeps (s s' : State lock) (p : Proc) : Prop where
  owner : s'.owner = s.owner
  cs : s'.cs p = true

theorem keeps_step (s : State lock) (e : Event) (p : Proc) (hp : s.cs p = true)
    (hown : s.owner = some p) (hlive : s.os.table p.pid = some p.tok)
    (hrel : e ≠ Event.release p.pid) (hexit : e ≠ Event.exit p.pid) :
    Keeps s (step lock s e) p := by
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
    have hg : grants lock s = false := by simp [grants, hown, hlive, lock]
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨rfl, hp⟩
    | some t0 =>
      simp only [step, hpid, hg, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, hp⟩
  | release pid =>
    have hne : pid ≠ p.pid := fun heq => hrel (by rw [heq])
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨rfl, hp⟩
    | some t0 =>
      have hio : lock.isOwner p ⟨pid, t0⟩ = false := by
        have hpne : p ≠ ⟨pid, t0⟩ := fun heq => hne (by rw [heq])
        simp [lock, hpne]
      simp only [step, hpid, hown, hio, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, hp⟩

theorem holder_keeps_lock : HolderKeepsLock lock := by
  intro evs e p hp hrel hexit
  rw [replay_snoc]
  obtain ⟨hown, hlive⟩ := (inv_all evs).csOwner p hp
  have k := keeps_step (replay lock evs) e p hp hown hlive hrel hexit
  exact ⟨k.owner, k.cs⟩

/-- Design A passes each law. -/
theorem a_passes : Passes designA :=
  ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock, Exp.can_refuse, Exp.can_enter⟩

/-- Design B passes each law. -/
theorem b_passes : Passes designB :=
  ⟨mutex, no_orphan_hold, holder_keeps_lock, can_refuse, can_enter⟩

/-- After `trace`, `who` is in the critical section for one design only. -/
theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
