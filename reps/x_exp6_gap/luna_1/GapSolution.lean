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

structure InvB (s : State designB) : Prop where
  freshT : ∀ (pid t : Nat), s.os.table pid = some t → t < s.os.next
  freshO : ∀ r : Proc, s.owner = some r → r.tok < s.os.next
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p ∧ s.os.table p.pid = some p.tok
  ownerCs : ∀ r : Proc, s.owner = some r → s.os.table r.pid = some r.tok → s.cs r = true

theorem invB_init : InvB (init designB) := by
  constructor <;> simp [init]

theorem invB_step (s : State designB) (e : Event) (h : InvB s) :
    InvB (step designB s e) := by
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
        · have ht : s.os.next = t := Option.some.inj hq'
          omega
        · have ht := hT q t hq'
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
        simp only [hne, ↓reduceIte]
        exact h2
      · intro r hr hlive
        have hlive' : (if r.pid = pid then some s.os.next else s.os.table r.pid) = some r.tok := hlive
        split at hlive'
        · have h1 : r.pid = pid := by assumption
          have h2 := hO r hr
          have h3 : s.os.next = r.tok := Option.some.inj hlive'
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
          simp only [hpne, ↓reduceIte]
          exact h2
      · intro r hr hlive
        have hlive' : (if r.pid = pid then none else s.os.table r.pid) = some r.tok := hlive
        split at hlive'
        · cases hlive'
        · rename_i hne
          have hcs := hOC r hr hlive'
          show (if r = ⟨pid, t0⟩ then false else s.cs r) = true
          have hrne : r ≠ ⟨pid, t0⟩ := by
            intro heq; apply hne; rw [heq]
          simp only [hrne, ↓reduceIte]
          exact hcs
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
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro q t hq; exact hT q t hq
        · intro r hr
          show r.tok < s.os.next
          have hr' : (⟨pid, t0⟩ : Proc) = r := Option.some.inj hr
          rw [← hr']; exact hT pid t0 hpid
        · intro p hp
          have hp' : (if p = ⟨pid, t0⟩ then true else s.cs p) = true := hp
          split at hp'
          · rename_i heq; subst heq; exact ⟨rfl, hpid⟩
          · rw [hempty p] at hp'; cases hp'
        · intro r hr hlive
          have hr' : (⟨pid, t0⟩ : Proc) = r := Option.some.inj hr
          show (if r = ⟨pid, t0⟩ then true else s.cs r) = true
          subst hr'; simp
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      cases ho : s.owner with
      | none => simp only [step, hpid, ho]; exact ⟨hT, hO, hC, hOC⟩
      | some r => simp only [step, hpid, ho, designB]; exact ⟨hT, hO, hC, hOC⟩

theorem invB_all (evs : List Event) : InvB (replay designB evs) :=
  Exp.replay_inv InvB invB_init invB_step evs

theorem b_mutex : Mutex designB := by
  intro evs p q hp hq
  have h := invB_all evs
  exact Option.some.inj ((h.csOwner p hp).1.symm.trans (h.csOwner q hq).1)

theorem b_no_orphan_hold : NoOrphanHold designB := by
  intro evs hg
  have h := invB_all evs
  cases ho : (replay designB evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(designB.alive (replay designB evs).os r)) = false := by
      simpa [grants, ho] using hg
    have hlive : (replay designB evs).os.table r.pid = some r.tok := by
      simpa [designB] using hg'
    exact ⟨r, h.ownerCs r ho hlive, hlive⟩

theorem b_holder_keeps : HolderKeepsLock designB := by
  intro evs e p hp hrel hexit
  rw [Exp.replay_snoc]
  obtain ⟨hown, hlive⟩ := (invB_all evs).csOwner p hp
  cases e with
  | spawn pid =>
    cases hpid : (replay designB evs).os.table pid <;> simp [step, hpid, hp]
  | exit pid =>
    have hne : pid ≠ p.pid := fun heq => hexit (by rw [heq])
    cases hpid : (replay designB evs).os.table pid with
    | none => simp [step, hpid, hp]
    | some t0 =>
      have hpne : p ≠ ⟨pid, t0⟩ := by
        intro heq; apply hne; cases heq; rfl
      simp [step, hpid]
      unfold setCS
      split <;> simp_all
  | acquire pid =>
    have hg : grants designB (replay designB evs) = false := by
      simp only [grants, hown]
      have ha : designB.alive (replay designB evs).os p = true := by
        change decide ((replay designB evs).os.table p.pid = some p.tok) = true
        simp [hlive]
      rw [ha]
      rfl
    cases hpid : (replay designB evs).os.table pid with
    | none => simp [step, hpid, hp]
    | some t0 => simp [step, hpid, hg, hp]
  | release pid =>
    cases hpid : (replay designB evs).os.table pid with
    | none => simp [step, hpid, hp]
    | some t0 =>
      cases ho : (replay designB evs).owner with
      | none => simp [step, hpid, ho, hp]
      | some r =>
        simp only [step, hpid, ho]
        simp [designB]
        exact ⟨ho, hp⟩

theorem b_can_refuse : CanRefuse designB := ⟨[.spawn 5, .acquire 5], by decide⟩

theorem b_can_enter : CanEnter designB :=
  ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩

theorem b_passes : Passes designB := by
  exact ⟨b_mutex, b_no_orphan_hold, b_holder_keeps, b_can_refuse, b_can_enter⟩

theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
