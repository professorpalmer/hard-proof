import SyncLaws

open SyncLaws

namespace SyncComplete

theorem list_eq_of_map_key (x y : List Entry) (hk : x.map key = y.map key)
    (hp : ∀ a ∈ x, ∀ b ∈ y, key a = key b → a = b) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b ys => simp at hk
  | cons a xs ih =>
    cases y with
    | nil => simp at hk
    | cons b ys =>
      simp only [List.map_cons, List.cons.injEq] at hk
      obtain ⟨h1, h2⟩ := hk
      have hab : a = b := hp a (by simp) b (by simp) h1
      subst hab
      congr 1
      exact ih ys h2 (fun a' ha' b' hb' hk' =>
        hp a' (List.mem_cons_of_mem _ ha') b' (List.mem_cons_of_mem _ hb') hk')

theorem entry_ext (a b : Entry) (h1 : a.id = b.id) (h2 : a.adapter = b.adapter)
    (h3 : a.model = b.model) (h4 : a.enabled = b.enabled) : a = b := by
  cases a; cases b; simp_all

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨kf, _, _, df, lf, ef, _, xf⟩ := hf
  obtain ⟨kg, _, _, dg, lg, eg, _, xg⟩ := hg
  obtain ⟨af, haf⟩ := kf c st r
  obtain ⟨ag, hag⟩ := kg c st r
  rw [haf, hag]
  congr 1
  apply list_eq_of_map_key
  · rw [xf c st r af haf, xg c st r ag hag]
  · intro a ha b hb hk
    simp only [key, Prod.mk.injEq] at hk
    obtain ⟨hi, hadp, hm⟩ := hk
    apply entry_ext a b hi hadp hm
    cases hen : c.enable with
    | false => rw [df c st r af hen haf a ha, dg c st r ag hen hag b hb]
    | true =>
      cases hl : c.locked a.adapter with
      | true =>
        have hl' : c.locked b.adapter = true := by rw [← hadp]; exact hl
        rw [lf c st r af haf a ha hl, lg c st r ag hag b hb hl']
      | false =>
        have hl' : c.locked b.adapter = false := by rw [← hadp]; exact hl
        obtain ⟨s, hs, hsid, hsen⟩ := ef c st r af hd hen haf a ha hl
        obtain ⟨s', hs', hsid', hsen'⟩ := eg c st r ag hd hen hag b hb hl'
        have : s = s' := hd s hs s' hs' (by rw [hsid, hsid', hi])
        subst this
        rw [hsen, hsen']

end SyncComplete
