/-
  First-Class Relationships as a Representation Threshold
  Lean 4 development for Theorem 2 (b), (c) of the paper
  (core Lean, no Mathlib).

  Build: `lake build`, on the toolchain pinned in lean-toolchain.

  Model: a representation with one relationship construct whose
  participant slots may or may not hold relationships.

  Proved:
    * P3 (evidential-basis clause) and P4 each imply COMPOSE.
    * COMPOSE plus a relationship builder (here: FC) yields
      representations of P3 and P4.
    * Given a builder, P4 holds iff FC holds (likewise P3).
    * A relational-style construct (n-ary rows, no references to rows)
      has a builder but no COMPOSE, hence no P4.

  Not modelled (argued on paper only): STORE, RETRIEVE, QUERY, ATTACH,
  arity, confidence values and valid time; Theorem 2 (a); Lemma 1.
-/

/-- An abstract knowledge representation system with one relationship
    construct. `Slot` is what a participant position can hold; `asRel`
    reads a slot back as a relationship when the slot refers to one. -/
structure System where
  Ent   : Type
  Rel   : Type
  Slot  : Type
  Attr  : Type
  ofEnt : Ent → Slot
  parts : Rel → List Slot
  attrs : Rel → List Attr
  asRel : Slot → Option Rel

/-- COMPOSE: every relationship can occupy a participant slot from which
    it can be read back. -/
@[reducible] def Compose (S : System) : Prop :=
  ∃ ref : S.Rel → S.Slot, ∀ r, S.asRel (ref r) = some r

/-- The system can form a relationship from any list of participant slots
    and attributes. -/
structure Builder (S : System) where
  build       : List S.Slot → List S.Attr → S.Rel
  parts_build : ∀ ps as, S.parts (build ps as) = ps

/-- First-class relationships: COMPOSE together with a builder. -/
@[reducible] def FC (S : System) : Prop :=
  Compose S ∧ Nonempty (Builder S)

/-- P3, evidential-basis clause: for every relationship, an assessment of
    it can be represented as a relationship among whose participants the
    assessed relationship can be found. -/
structure P3 (S : System) where
  assess    : S.Rel → S.Rel
  assess_in : ∀ r, ∃ x, x ∈ S.parts (assess r) ∧ S.asRel x = some r

/-- P4: for any two relationships, a causal relationship among whose
    participants both can be found. -/
structure P4 (S : System) where
  causal    : S.Rel → S.Rel → S.Rel
  cause_in  : ∀ r₁ r₂, ∃ x, x ∈ S.parts (causal r₁ r₂) ∧ S.asRel x = some r₁
  effect_in : ∀ r₁ r₂, ∃ x, x ∈ S.parts (causal r₁ r₂) ∧ S.asRel x = some r₂

-- ============================================================================
-- Theorem 2 (b): P3 ⇒ COMPOSE and P4 ⇒ COMPOSE
-- ============================================================================

theorem p3_compose (S : System) (h : P3 S) : Compose S :=
  ⟨fun r => Classical.choose (h.assess_in r),
   fun r => (Classical.choose_spec (h.assess_in r)).2⟩

theorem p4_compose (S : System) (h : P4 S) : Compose S :=
  ⟨fun r => Classical.choose (h.cause_in r r),
   fun r => (Classical.choose_spec (h.cause_in r r)).2⟩

-- ============================================================================
-- Theorem 2 (c): FC ⇒ P3 and FC ⇒ P4
-- ============================================================================

noncomputable def FC.ref {S : System} (h : FC S) : S.Rel → S.Slot :=
  Classical.choose h.1

theorem FC.ref_spec {S : System} (h : FC S) (r : S.Rel) :
    S.asRel (FC.ref h r) = some r :=
  Classical.choose_spec h.1 r

noncomputable def FC.builder {S : System} (h : FC S) : Builder S :=
  Classical.choice h.2

noncomputable def fc_to_p3 (S : System) (h : FC S) : P3 S where
  assess r := (FC.builder h).build [FC.ref h r] []
  assess_in r :=
    ⟨FC.ref h r, by simp [(FC.builder h).parts_build], FC.ref_spec h r⟩

noncomputable def fc_to_p4 (S : System) (h : FC S) : P4 S where
  causal r₁ r₂ := (FC.builder h).build [FC.ref h r₁, FC.ref h r₂] []
  cause_in r₁ r₂ :=
    ⟨FC.ref h r₁, by simp [(FC.builder h).parts_build], FC.ref_spec h r₁⟩
  effect_in r₁ r₂ :=
    ⟨FC.ref h r₂, by simp [(FC.builder h).parts_build], FC.ref_spec h r₂⟩

-- ============================================================================
-- Corollary: with a builder, P4 holds iff FC holds (likewise P3)
-- ============================================================================

theorem p4_iff_fc (S : System) (B : Builder S) : Nonempty (P4 S) ↔ FC S :=
  ⟨fun ⟨p⟩ => ⟨p4_compose S p, ⟨B⟩⟩, fun h => ⟨fc_to_p4 S h⟩⟩

theorem p3_iff_fc (S : System) (B : Builder S) : Nonempty (P3 S) ↔ FC S :=
  ⟨fun ⟨p⟩ => ⟨p3_compose S p, ⟨B⟩⟩, fun h => ⟨fc_to_p3 S h⟩⟩

-- ============================================================================
-- Below the threshold: n-ary rows without references to rows
-- ============================================================================

/-- Relational-style system: a relationship is a row of entity values;
    no slot can refer to a row. -/
def relational : System where
  Ent   := Nat
  Rel   := List Nat
  Slot  := Nat
  Attr  := Unit
  ofEnt := id
  parts := id
  attrs := fun _ => []
  asRel := fun _ => none

def relationalBuilder : Builder relational where
  build ps _ := ps
  parts_build _ _ := rfl

theorem relational_not_compose : ¬ Compose relational := by
  intro hc
  cases hc with
  | intro ref h =>
    have h1 := h ([] : List Nat)
    simp [relational] at h1

theorem relational_not_p4 : ¬ Nonempty (P4 relational) :=
  fun ⟨p⟩ => relational_not_compose (p4_compose relational p)

-- ============================================================================
-- Supporting fact for Lemma 1 (attachment): a binary edge drawn from
-- three distinct participants leaves one participant out.

-- ============================================================================

inductive KRObject (Entity : Type) : Type where
  | entity : Entity → KRObject Entity
  | rel    : List (KRObject Entity) → KRObject Entity

theorem binary_decomposition_failure
    {Entity : Type}
    (p₁ p₂ p₃ : KRObject Entity)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (src dst : KRObject Entity)
    (hsrc : src ∈ [p₁, p₂, p₃]) (hdst : dst ∈ [p₁, p₂, p₃])
    : ∃ (p : KRObject Entity), p ∈ [p₁, p₂, p₃] ∧ p ≠ src ∧ p ≠ dst := by
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hsrc hdst ⊢
  rcases hsrc with rfl | rfl | rfl <;> rcases hdst with rfl | rfl | rfl
  · exact ⟨p₂, Or.inr (Or.inl rfl), Ne.symm h12, Ne.symm h12⟩
  · exact ⟨p₃, Or.inr (Or.inr rfl), Ne.symm h13, Ne.symm h23⟩
  · exact ⟨p₂, Or.inr (Or.inl rfl), Ne.symm h12, h23⟩
  · exact ⟨p₃, Or.inr (Or.inr rfl), Ne.symm h23, Ne.symm h13⟩
  · exact ⟨p₁, Or.inl rfl, h12, h12⟩
  · exact ⟨p₁, Or.inl rfl, h12, h13⟩
  · exact ⟨p₂, Or.inr (Or.inl rfl), h23, Ne.symm h12⟩
  · exact ⟨p₁, Or.inl rfl, h13, h12⟩
  · exact ⟨p₁, Or.inl rfl, h13, h13⟩
