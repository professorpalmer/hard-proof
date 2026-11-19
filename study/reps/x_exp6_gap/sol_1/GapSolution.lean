import Laws
import Solution

open Laws

namespace Gap

def designA : LockImpl := Exp.lock

def designB : LockImpl :=
  { Exp.lock with isOwner := fun _ _ => false }

def trace : List Event := [.spawn 5, .acquire 5, .release 5]

def who : Proc := ⟨5, 0⟩

theorem a_passes : Passes designA := by
  exact ⟨Exp.mutex, Exp.no_orphan_hold, Exp.holder_keeps_lock,
    Exp.can_refuse, Exp.can_enter⟩

private def withoutReleases : List Event → List Event
  | [] => []
  | .release _ :: es => withoutReleases es
  | e :: es => e :: withoutReleases es

private def asA (s : State designB) : State Exp.lock :=
  { os := s.os, owner := s.owner, cs := s.cs }

private theorem grants_asA (s : State designB) :
    grants Exp.lock (asA s) = grants designB s := by
  cases s with
  | mk os owner cs =>
    cases owner <;> rfl

private theorem asA_step_nonrelease (s : State designB) (e : Event)
    (h : ∀ pid, e ≠ .release pid) :
    asA (step designB s e) = step Exp.lock (asA s) e := by
  cases s with
  | mk os owner cs =>
  cases e with
  | spawn pid =>
    cases hpid : os.table pid <;>
      simp [step, hpid, asA, designB, Exp.lock]
  | exit pid =>
    cases hpid : os.table pid <;>
      simp [step, hpid, asA, designB, Exp.lock]
  | acquire pid =>
    cases hpid : os.table pid with
    | none => simp [step, hpid, asA, designB, Exp.lock]
    | some t =>
      cases howner : owner with
      | none => simp [step, hpid, howner, asA, designB, Exp.lock, grants]
      | some r =>
        simp [step, hpid, howner, asA, designB, Exp.lock, grants]
        split <;> rfl
  | release pid => exact absurd rfl (h pid)

private theorem step_release (s : State designB) (pid : Nat) :
    step designB s (.release pid) = s := by
  cases hpid : s.os.table pid with
  | none => simp only [step, hpid]
  | some t =>
    cases howner : s.owner with
    | none => simp only [step, hpid, howner]
    | some r =>
      simp only [step, hpid, howner]
      change (if false then _ else s) = s
      rfl

private theorem asA_step_release (s : State designB) (pid : Nat) :
    asA (step designB s (.release pid)) = asA s := by
  rw [step_release]

private theorem withoutReleases_append (xs ys : List Event) :
    withoutReleases (xs ++ ys) = withoutReleases xs ++ withoutReleases ys := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp [withoutReleases, ih]

private theorem foldl_withoutReleases (evs : List Event) (s : State designB) :
    asA (evs.foldl (step designB) s) =
      (withoutReleases evs).foldl (step Exp.lock) (asA s) := by
  induction evs generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | spawn pid =>
      simp only [withoutReleases, List.foldl_cons]
      rw [ih, asA_step_nonrelease]
      intro q h
      cases h
    | exit pid =>
      simp only [withoutReleases, List.foldl_cons]
      rw [ih, asA_step_nonrelease]
      intro q h
      cases h
    | acquire pid =>
      simp only [withoutReleases, List.foldl_cons]
      rw [ih, asA_step_nonrelease]
      intro q h
      cases h
    | release pid =>
      simp only [withoutReleases, List.foldl_cons]
      rw [ih, asA_step_release]

private theorem replay_withoutReleases (evs : List Event) :
    asA (replay designB evs) = replay Exp.lock (withoutReleases evs) := by
  exact foldl_withoutReleases evs (init designB)

private theorem replay_cs (evs : List Event) (p : Proc) :
    (replay designB evs).cs p = (replay Exp.lock (withoutReleases evs)).cs p := by
  exact congrArg (fun s => s.cs p) (replay_withoutReleases evs)

private theorem replay_owner (evs : List Event) :
    (replay designB evs).owner = (replay Exp.lock (withoutReleases evs)).owner := by
  exact congrArg State.owner (replay_withoutReleases evs)

private theorem replay_os (evs : List Event) :
    (replay designB evs).os = (replay Exp.lock (withoutReleases evs)).os := by
  exact congrArg State.os (replay_withoutReleases evs)

private theorem replay_grants (evs : List Event) :
    grants designB (replay designB evs) =
      grants Exp.lock (replay Exp.lock (withoutReleases evs)) := by
  rw [grants, grants, replay_owner, replay_os]
  cases (replay Exp.lock (withoutReleases evs)).owner <;>
    simp [designB, Exp.lock]

theorem b_passes : Passes designB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro evs p q hp hq
    rw [replay_cs] at hp hq
    exact Exp.mutex (withoutReleases evs) p q hp hq
  · intro evs hg
    rw [replay_grants] at hg
    obtain ⟨q, hcs, hlive⟩ := Exp.no_orphan_hold (withoutReleases evs) hg
    refine ⟨q, ?_, ?_⟩
    · rwa [replay_cs]
    · rw [OS.live, replay_os]
      exact hlive
  · intro evs e p hp hrel hexit
    rw [replay_cs] at hp
    cases e with
    | release pid =>
      rw [Exp.replay_snoc]
      rw [step_release]
      exact ⟨rfl, by rwa [replay_cs]⟩
    | spawn pid =>
      obtain ⟨ho, hc⟩ :=
        Exp.holder_keeps_lock (withoutReleases evs) (.spawn pid) p hp hrel hexit
      constructor
      · rw [replay_owner, replay_owner]
        rw [withoutReleases_append]
        exact ho
      · rw [replay_cs]
        rw [withoutReleases_append]
        exact hc
    | exit pid =>
      obtain ⟨ho, hc⟩ :=
        Exp.holder_keeps_lock (withoutReleases evs) (.exit pid) p hp hrel hexit
      constructor
      · rw [replay_owner, replay_owner]
        rw [withoutReleases_append]
        exact ho
      · rw [replay_cs]
        rw [withoutReleases_append]
        exact hc
    | acquire pid =>
      obtain ⟨ho, hc⟩ :=
        Exp.holder_keeps_lock (withoutReleases evs) (.acquire pid) p hp hrel hexit
      constructor
      · rw [replay_owner, replay_owner]
        rw [withoutReleases_append]
        exact ho
      · rw [replay_cs]
        rw [withoutReleases_append]
        exact hc
  · exact ⟨[.spawn 5, .acquire 5], by decide⟩
  · exact ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩

theorem differ : (replay designA trace).cs who ≠ (replay designB trace).cs who := by
  decide

end Gap
