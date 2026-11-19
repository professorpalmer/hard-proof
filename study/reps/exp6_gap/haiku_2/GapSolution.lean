/-
Hard Proof, experiment 6. AGENT-OWNED FILE.

The adversary's answer to the gap challenge.

Design A is the lock from `Solution.lean`. Design B has the same record and the
same liveness test, but its release never clears the owner (`isOwner` is always
false). Both designs pass every law. After `acquire 1` and `release 1`, process
`1:0` is outside the critical section in design A and still inside in design B.
-/
import Laws
import Solution

open Laws

namespace Gap

/-- The first design. -/
def designA : LockImpl := Exp.lock

/-- The second design. Same record and liveness test as `designA`, but release
never recognises the owner, so the owner and the critical section stay set. -/
def designB : LockImpl where
  Rec := Proc
  record p := p
  alive os r := decide (os.table r.pid = some r.tok)
  isOwner _ _ := false

/-- The sequence of events on which the two designs differ. -/
def trace : List Event := [.spawn 1, .acquire 1, .release 1]

/-- The process that is inside for one design and outside for the other. -/
def who : Proc := ⟨1, 0⟩

/-! ## Invariant for design B -/

structure InvB (s : State designB) : Prop where
  freshT : ∀ (pid t : Nat), s.os.table pid = some t → t < s.os.next
  freshO : ∀ r : Proc, s.owner = some r → r.tok < s.os.next
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p ∧ s.os.table p.pid = some p.tok
  ownerCs : ∀ r : Proc, s.owner = some r → s.os.table r.pid = some r.tok → s.cs r = true

theorem invB_init : InvB (init designB) := by
  constructor <;> simp [init]

theorem release_noop_B (s : State designB) (pid : Nat) :
    step designB s (.release pid) = s := by
  cases hpid : s.os.table pid with
  | none => simp [step, hpid]
  | some t0 =>
    cases ho : s.owner with
    | none => simp [step, hpid, ho]
    | some r => simp [step, hpid, ho, designB]; rfl

theorem invB_step (s : State designB) (e : Event) (h : InvB s) : InvB (step designB s e) := by
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
            exact Exp.proc_eq heq (Option.some.inj h2).symm
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
      cases hg : grants designB s with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩
      | true =>
        simp only [↓reduceIte]
        have hempty : ∀ p : Proc, s.cs p = false := by
          intro p
          cases hcs : s.cs p with
          | false => rfl
          | true =>
            obtain ⟨h1, h2⟩ := hC p hcs
            simp [grants, h1, h2, designB] at hg
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
    rw [release_noop_B]
    exact ⟨hT, hO, hC, hOC⟩

theorem mutex_B : Mutex designB := by
  intro evs p q hp hq
  have h := Exp.replay_inv InvB invB_init invB_step evs
  have h1 := (h.csOwner p hp).1
  have h2 := (h.csOwner q hq).1
  rw [h1] at h2
  exact Option.some.inj h2

theorem noOrphan_B : NoOrphanHold designB := by
  intro evs hg
  have h := Exp.replay_inv InvB invB_init invB_step evs
  cases ho : (replay designB evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(designB.alive (replay designB evs).os r)) = false := by
      simpa [grants, ho] using hg
    have halive : (replay designB evs).os.table r.pid = some r.tok := by
      simpa [designB] using hg'
    exact ⟨r, h.ownerCs r ho halive, halive⟩

/-- One step keeps the owner and keeps `p` in the critical section, when `p` is
the live owner. -/
theorem keep_step_B (s : State designB) (e : Event) (p : Proc) (hp : s.cs p = true)
    (hown : s.owner = some p) (hlive : s.os.table p.pid = some p.tok)
    (hrel : e ≠ Event.release p.pid) (hexit : e ≠ Event.exit p.pid) :
    (step designB s e).owner = s.owner ∧ (step designB s e).cs p = true := by
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid with
    | some t0 => simp [step, hpid, hp]
    | none => simp [step, hpid, hp]
  | exit pid =>
    have hne : pid ≠ p.pid := fun heq => hexit (by rw [heq])
    cases hpid : s.os.table pid with
    | none => simp [step, hpid, hp]
    | some t0 =>
      have hpne : p ≠ ⟨pid, t0⟩ := fun heq => hne (by rw [heq])
      simp [step, hpid, setCS, hpne, hp]
  | acquire pid =>
    have hg : grants designB s = false := by simp [grants, hown, hlive, designB]
    cases hpid : s.os.table pid with
    | none => simp [step, hpid, hp]
    | some t0 => simp [step, hpid, hg, hp]
  | release pid =>
    rw [release_noop_B]
    exact ⟨rfl, hp⟩

theorem holder_B : HolderKeepsLock designB := by
  intro evs e p hp hrel hexit
  obtain ⟨hown, hlive⟩ := (Exp.replay_inv InvB invB_init invB_step evs).csOwner p hp
  rw [Exp.replay_snoc]
  exact keep_step_B (replay designB evs) e p hp hown hlive hrel hexit

theorem can_refuse_B : CanRefuse designB := ⟨[.spawn 5, .acquire 5], by decide⟩

theorem can_enter_B : CanEnter designB := ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩

/-! ## The two statements -/

/-- The first design passes each law. -/
theorem a_passes : Passes designA :=
  ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock, Exp.can_refuse, Exp.can_enter⟩

/-- The second design passes each law. -/
theorem b_passes : Passes designB :=
  ⟨mutex_B, noOrphan_B, holder_B, can_refuse_B, can_enter_B⟩

/-- After `trace`, `who` is in the critical section for one design only. -/
theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
