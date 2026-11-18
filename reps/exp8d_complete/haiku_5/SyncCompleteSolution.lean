import SyncLaws

open SyncLaws

namespace SyncComplete

/-- Two rows with one key and one `enabled` value are equal. -/
theorem entry_eq_of (a b : Entry) (hk : key a = key b) (he : a.enabled = b.enabled) : a = b := by
  rcases a with ⟨ia, aa, ma, ea⟩
  rcases b with ⟨ib, ab, mb, eb⟩
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨h1, h2, h3⟩ := hk
  dsimp only at he
  subst h1
  subst h2
  subst h3
  subst he
  rfl

/-- Two added lists with one key list and one `enabled` value per key are equal. -/
theorem same_of_keys : ∀ (A B : List Entry), A.map key = B.map key →
    (∀ a ∈ A, ∀ b ∈ B, key a = key b → a.enabled = b.enabled) → A = B
  | [], [], _, _ => rfl
  | [], _ :: _, hk, _ => by simp at hk
  | _ :: _, [], hk, _ => by simp at hk
  | a :: A, b :: B, hk, hen => by
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨hab, hk'⟩ := hk
    have he : a.enabled = b.enabled := hen a (by simp) b (by simp) hab
    have hrest : A = B := same_of_keys A B hk' (fun x hx y hy hxy =>
      hen x (by simp [hx]) y (by simp [hy]) hxy)
    rw [entry_eq_of a b hab he, hrest]

/-- The `enabled` value of an added row, from one design that passes the laws. -/
theorem enabled_value (f : SyncImpl) (hdef : DisabledByDefault f) (hlock : LockedStaysDisabled f)
    (heks : EnableKeepsStarterState f) (c : Config) (st r A : List Entry)
    (hd : DistinctIds st) (hA : f c st r = r ++ A) (a : Entry) (ha : a ∈ A)
    (s : Entry) (hs : s ∈ st) (hid : s.id = a.id) :
    a.enabled = (c.enable && !c.locked a.adapter && s.enabled) := by
  cases h1 : c.enable with
  | false => simp [hdef c st r A h1 hA a ha]
  | true =>
    cases h2 : c.locked a.adapter with
    | true => simp [hlock c st r A hA a ha h2]
    | false =>
      obtain ⟨s', hs', hid', hen'⟩ := heks c st r A hd h1 hA a ha h2
      have hss : s' = s := hd s' hs' s hs (hid'.trans hid.symm)
      simp [hen', hss]

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  unfold Passes at hf hg
  obtain ⟨krf, -, -, dbdf, lsdf, eksf, -, eaf⟩ := hf
  obtain ⟨krg, -, -, dbdg, lsdg, eksg, -, eag⟩ := hg
  obtain ⟨A, hA⟩ := krf c st r
  obtain ⟨B, hB⟩ := krg c st r
  rw [hA, hB]
  congr 1
  apply same_of_keys
  · rw [eaf c st r A hA, eag c st r B hB]
  · intro a ha b hb hab
    have hka : key a ∈ (st.filter (absent r)).map key := by
      rw [← eaf c st r A hA]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    have hkb : key b ∈ (st.filter (absent r)).map key := by
      rw [← eag c st r B hB]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨s, hsK, hsk⟩ := List.mem_map.mp hka
    obtain ⟨t, htK, htk⟩ := List.mem_map.mp hkb
    have hsst : s ∈ st := (List.mem_filter.mp hsK).1
    have htst : t ∈ st := (List.mem_filter.mp htK).1
    have hkst : key s = key t := hsk.trans (hab.trans htk.symm)
    have hst : s = t := hd s hsst t htst (congrArg (fun p => p.1) hkst)
    have hadp : a.adapter = b.adapter := congrArg (fun p => p.2.1) hab
    have hida : s.id = a.id := congrArg (fun p => p.1) hsk
    have hidb : t.id = b.id := congrArg (fun p => p.1) htk
    rw [enabled_value f dbdf lsdf eksf c st r A hd hA a ha s hsst hida,
      enabled_value g dbdg lsdg eksg c st r B hd hB b hb t htst hidb, hadp, hst]

end SyncComplete
