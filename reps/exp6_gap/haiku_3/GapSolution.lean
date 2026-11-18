import Laws
import Solution

open Laws

namespace Gap

/-- The first design: the lock from `Solution.lean`. -/
def designA : LockImpl := Exp.lock

/-- The second design. It uses the same alive test and the same owner record as
`designA`. Its release never clears the owner, so a release does not take the
process out of the critical section. -/
def designB : LockImpl where
  Rec := Proc
  record p := p
  alive os r := decide (os.table r.pid = some r.tok)
  isOwner _ _ := false

/-- Spawn pid 5, acquire, then release. -/
def trace : List Event := [.spawn 5, .acquire 5, .release 5]

/-- The process with pid 5 and start token 0. -/
def who : Proc := ⟨5, 0⟩

/-! ## Design A passes each law: reuse the proofs of `Solution.lean`. -/

theorem a_passes : Passes designA := by
  unfold Passes designA
  exact ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock, Exp.can_refuse, Exp.can_enter⟩

/-! ## Design B passes each law -/

theorem step_release (s : State designB) (pid : Nat) :
    step designB s (.release pid) = s := by
  simp only [step]
  cases h1 : s.os.table pid <;> cases h2 : s.owner <;> simp only [h1, h2] <;> rfl

theorem replay_snoc_B (evs : List Event) (e : Event) :
    replay designB (evs ++ [e]) = step designB (replay designB evs) e := by
  simp [replay, List.foldl_append]

theorem foldl_inv_B (P : State designB → Prop)
    (hs : ∀ s e, P s → P (step designB s e)) :
    ∀ (evs : List Event) (s : State designB), P s → P (evs.foldl (step designB) s) := by
  intro evs
  induction evs with
  | nil => intro s h; exact h
  | cons e es ih => intro s h; exact ih _ (hs s e h)

theorem replay_inv_B (P : State designB → Prop)
    (h0 : P (init designB)) (hs : ∀ s e, P s → P (step designB s e)) (evs : List Event) :
    P (replay designB evs) :=
  foldl_inv_B P hs evs (init designB) h0

theorem proc_eq_B {p : Proc} {pid t : Nat} (h1 : p.pid = pid) (h2 : p.tok = t) :
    p = ⟨pid, t⟩ := by
  subst h1; subst h2; rfl

/-- The invariant for `designB`. -/
structure InvB (s : State designB) : Prop where
  freshT : ∀ (pid t : Nat), s.os.table pid = some t → t < s.os.next
  freshO : ∀ r : Proc, s.owner = some r → r.tok < s.os.next
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p ∧ s.os.table p.pid = some p.tok
  ownerCs : ∀ r : Proc, s.owner = some r → s.os.table r.pid = some r.tok → s.cs r = true

theorem inv_init_B : InvB (init designB) := by
  constructor <;> simp [init]

theorem inv_step_B (s : State designB) (e : Event) (h : InvB s) :
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
            exact proc_eq_B heq (Option.some.inj h2).symm
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
    rw [step_release]
    exact ⟨hT, hO, hC, hOC⟩

theorem inv_all_B (evs : List Event) : InvB (replay designB evs) :=
  replay_inv_B InvB inv_init_B inv_step_B evs

theorem mutex_B : Mutex designB := by
  intro evs p q hp hq
  have h := inv_all_B evs
  have h1 := (h.csOwner p hp).1
  have h2 := (h.csOwner q hq).1
  rw [h1] at h2
  exact Option.some.inj h2

theorem no_orphan_B : NoOrphanHold designB := by
  intro evs hg
  have h := inv_all_B evs
  cases ho : (replay designB evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(designB.alive (replay designB evs).os r)) = false := by
      simpa [grants, ho] using hg
    have halive : (replay designB evs).os.table r.pid = some r.tok := by
      simpa [designB] using hg'
    exact ⟨r, h.ownerCs r ho halive, halive⟩

/-- One step keeps the owner record and keeps `p` in the critical section,
unless the event is the exit of `p`. -/
theorem keeps_step_B (s : State designB) (e : Event) (p : Proc) (hp : s.cs p = true)
    (hown : s.owner = some p) (hlive : s.os.table p.pid = some p.tok)
    (hexit : e ≠ Event.exit p.pid) :
    (step designB s e).owner = s.owner ∧ (step designB s e).cs p = true := by
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid with
    | some t0 => simp only [step, hpid]; exact ⟨trivial, hp⟩
    | none => simp only [step, hpid]; exact ⟨trivial, hp⟩
  | exit pid =>
    have hne : pid ≠ p.pid := fun heq => hexit (by rw [heq])
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨trivial, hp⟩
    | some t0 =>
      simp only [step, hpid]
      have hpne : p ≠ ⟨pid, t0⟩ := fun heq => hne (by rw [heq])
      refine ⟨trivial, ?_⟩
      show (if p = ⟨pid, t0⟩ then false else s.cs p) = true
      simp only [hpne, ↓reduceIte]; exact hp
  | acquire pid =>
    have hg : grants designB s = false := by simp [grants, hown, hlive, designB]
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨trivial, hp⟩
    | some t0 =>
      simp only [step, hpid, hg, Bool.false_eq_true, ↓reduceIte]; exact ⟨trivial, hp⟩
  | release pid => rw [step_release]; exact ⟨rfl, hp⟩

theorem holder_keeps_lock_B : HolderKeepsLock designB := by
  intro evs e p hp _ hexit
  have hI := inv_all_B evs
  obtain ⟨hown, hlive⟩ := hI.csOwner p hp
  have k := keeps_step_B (replay designB evs) e p hp hown hlive hexit
  rw [replay_snoc_B]
  exact ⟨k.1, k.2⟩

theorem can_refuse_B : CanRefuse designB :=
  ⟨[.spawn 5, .acquire 5, .spawn 6, .acquire 6], by decide⟩

theorem can_enter_B : CanEnter designB :=
  ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩

theorem b_passes : Passes designB := by
  unfold Passes
  exact ⟨mutex_B, no_orphan_B, holder_keeps_lock_B, can_refuse_B, can_enter_B⟩

/-! ## The gap -/

/-- After `trace`, process `who` is in the critical section for design A only. -/
theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
