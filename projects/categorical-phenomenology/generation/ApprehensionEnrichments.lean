import Std

/- Exact, total, set-level enrichments. No quotient of semantic witness data.
   Proposition-valued law proofs use Lean's proof irrelevance. -/
namespace ApprehensionEnrichments
universe u v w

structure RawApp (Obj : Type u) (C : Obj → Type v) (A B : Obj) where
  content : Obj
  deriv : C B → C content
  occ : C A → C content

def Closure (Obj : Type u) (C : Obj → Type v) (B : Obj) :=
  Sigma fun X : Obj => C B → C X

def RawApp.toBase {Obj : Type u} {C : Obj → Type v} {A B : Obj}
    (i : RawApp Obj C A B) : Sigma fun c : Closure Obj C B => C A → C c.1 :=
  ⟨⟨i.content, i.deriv⟩, i.occ⟩

def RawApp.fromBase {Obj : Type u} {C : Obj → Type v} {A B : Obj}
    (i : Sigma fun c : Closure Obj C B => C A → C c.1) : RawApp Obj C A B :=
  ⟨i.1.1, i.1.2, i.2⟩

theorem raw_roundtrip {Obj : Type u} {C : Obj → Type v} {A B : Obj}
    (i : RawApp Obj C A B) : RawApp.fromBase i.toBase = i := rfl

theorem base_roundtrip {Obj : Type u} {C : Obj → Type v} {A B : Obj}
    (i : Sigma fun c : Closure Obj C B => C A → C c.1) :
    (RawApp.fromBase i).toBase = i := rfl

structure ArrowSystem (Obj : Type u) (C : Obj → Type v) where
  Hom : Obj → Obj → Type w
  map : {A B : Obj} → Hom A B → C A → C B
  ident : (A : Obj) → Hom A A
  comp : {A B D : Obj} → Hom B D → Hom A B → Hom A D
  map_ident : ∀ A, map (ident A) = id
  map_comp : ∀ {A B D} (g : Hom B D) (f : Hom A B),
    map (comp g f) = map g ∘ map f
  ident_comp : ∀ {A B} (f : Hom A B), comp (ident B) f = f
  comp_ident : ∀ {A B} (f : Hom A B), comp f (ident A) = f
  assoc : ∀ {A B D E} (h : Hom D E) (g : Hom B D) (f : Hom A B),
    comp (comp h g) f = comp h (comp g f)

structure App {Obj : Type u} {C : Obj → Type v}
    (E : ArrowSystem.{u,v,w} Obj C) (A B : Obj) where
  content : Obj
  deriv : E.Hom B content
  occ : E.Hom A content

def App.toBase {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : App E A B) :
    Sigma fun c : (Sigma fun X : Obj => E.Hom B X) => E.Hom A c.1 :=
  ⟨⟨i.content, i.deriv⟩, i.occ⟩

def App.fromBase {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : Sigma fun c : (Sigma fun X : Obj => E.Hom B X) => E.Hom A c.1) :
    App E A B := ⟨i.1.1, i.1.2, i.2⟩

theorem enriched_roundtrip {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : App E A B) : App.fromBase i.toBase = i := rfl

theorem enriched_base_roundtrip {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : Sigma fun c : (Sigma fun X : Obj => E.Hom B X) => E.Hom A c.1) :
    (App.fromBase i).toBase = i := rfl

def forget {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : App E A B) : RawApp Obj C A B :=
  ⟨i.content, E.map i.deriv, E.map i.occ⟩

structure Support {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} (i : App E A B) (j : App E B D) where
  lift : E.Hom j.content i.content
  factor : E.comp lift j.occ = i.deriv

def reground {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} (i : App E A B) (j : App E B D) (h : Support i j) : App E A D :=
  ⟨i.content, E.comp h.lift j.deriv, i.occ⟩

theorem support_forgets {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} {i : App E A B} {j : App E B D} (h : Support i j) :
    E.map i.deriv = E.map h.lift ∘ E.map j.occ := by
  rw [← h.factor, E.map_comp]

theorem reground_forgets {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} (i : App E A B) (j : App E B D) (h : Support i j) :
    forget (reground i j h) =
      RawApp.mk i.content (E.map h.lift ∘ E.map j.deriv) (E.map i.occ) := by
  simp only [forget, reground, E.map_comp]

def canonical {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (f : E.Hom B A) : App E A B := ⟨A, f, E.ident A⟩

def canonicalSupport {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} (g : E.Hom B A) (f : E.Hom D B) :
    Support (canonical g) (canonical f) := ⟨g, E.comp_ident g⟩

theorem canonical_comp {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} (g : E.Hom B A) (f : E.Hom D B) :
    reground (canonical g) (canonical f) (canonicalSupport g f) =
      canonical (E.comp g f) := rfl

def extendSupport {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D F : Obj} {i : App E A B} {j : App E B D} {k : App E D F}
    (h : Support i j) (l : Support j k) : Support (reground i j h) k where
  lift := E.comp h.lift l.lift
  factor := by
    change E.comp (E.comp h.lift l.lift) k.occ = E.comp h.lift j.deriv
    rw [E.assoc, l.factor]

def slideSupport {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D F : Obj} {i : App E A B} {j : App E B D} {k : App E D F}
    (h : Support i j) (l : Support j k) : Support i (reground j k l) :=
  ⟨h.lift, h.factor⟩

theorem reground_assoc {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D F : Obj} (i : App E A B) (j : App E B D) (k : App E D F)
    (h : Support i j) (l : Support j k) :
    reground (reground i j h) k (extendSupport h l) =
      reground i (reground j k l) (slideSupport h l) := by
  simp only [reground, extendSupport, slideSupport, E.assoc]

def rightSupport {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : App E A B) : Support i (canonical (E.ident B)) :=
  ⟨i.deriv, E.comp_ident i.deriv⟩

theorem reground_right_unit {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B : Obj} (i : App E A B) :
    reground i (canonical (E.ident B)) (rightSupport i) = i := by
  cases i
  simp only [reground, canonical, rightSupport, E.comp_ident]

theorem canonical_lift {Obj : Type u} {C : Obj → Type v} {E : ArrowSystem Obj C}
    {A B D : Obj} (g : E.Hom B A) (f : E.Hom D B)
    (h : Support (canonical g) (canonical f)) : h.lift = g := by
  have hh := h.factor
  simpa only [canonical, E.comp_ident] using hh

structure Lens (S V : Type u) where
  get : S → V
  put : S → V → S
  get_put : ∀ s, put s (get s) = s
  put_get : ∀ s v, get (put s v) = v

namespace Lens
theorem ext {S V : Type u} {f g : Lens S V}
    (hg : f.get = g.get) (hp : f.put = g.put) : f = g := by
  cases f; cases g; cases hg; cases hp; rfl

def ident (S : Type u) : Lens S S where
  get := id
  put := fun _ v => v
  get_put := fun _ => rfl
  put_get := fun _ _ => rfl

def comp {S V W : Type u} (g : Lens V W) (f : Lens S V) : Lens S W where
  get := g.get ∘ f.get
  put := fun s w => f.put s (g.put (f.get s) w)
  get_put := by intro s; dsimp; rw [g.get_put, f.get_put]
  put_get := by intro s w; dsimp; rw [f.put_get, g.put_get]

theorem ident_comp {S V : Type u} (f : Lens S V) : comp (ident V) f = f :=
  ext rfl rfl
theorem comp_ident {S V : Type u} (f : Lens S V) : comp f (ident S) = f :=
  ext rfl rfl
theorem assoc {S V W Z : Type u} (h : Lens W Z) (g : Lens V W) (f : Lens S V) :
    comp (comp h g) f = comp h (comp g f) := ext rfl rfl

def PutPut {S V : Type u} (f : Lens S V) : Prop :=
  ∀ s v v', f.put (f.put s v) v' = f.put s v'

theorem ident_putPut (S : Type u) : PutPut (ident S) := fun _ _ _ => rfl

theorem comp_putPut {S V W : Type u} (g : Lens V W) (f : Lens S V)
    (hg : PutPut g) (hf : PutPut f) : PutPut (comp g f) := by
  intro s w w'
  change f.put (f.put s (g.put (f.get s) w))
    (g.put (f.get (f.put s (g.put (f.get s) w))) w') =
    f.put s (g.put (f.get s) w')
  rw [f.put_get, hf, hg]

def system : ArrowSystem (Type u) (fun S => S) where
  Hom := Lens
  map := Lens.get
  ident := ident
  comp := comp
  map_ident := fun _ => rfl
  map_comp := fun _ _ => rfl
  ident_comp := ident_comp
  comp_ident := comp_ident
  assoc := assoc
end Lens

structure ResponseModel where
  State : Type u
  Context : Type u
  Intervention : Type u
  idle : Intervention
  response : Context → Intervention → State

structure CausalMap (M N : ResponseModel.{u}) where
  state : M.State → N.State
  context : M.Context → N.Context
  intervention : M.Intervention → N.Intervention
  idle_law : intervention M.idle = N.idle
  commutes : ∀ u i, state (M.response u i) =
    N.response (context u) (intervention i)

namespace CausalMap
theorem ext {M N : ResponseModel.{u}} {f g : CausalMap M N}
    (hs : f.state = g.state) (hc : f.context = g.context)
    (hi : f.intervention = g.intervention) : f = g := by
  cases f; cases g; cases hs; cases hc; cases hi; rfl

def ident (M : ResponseModel.{u}) : CausalMap M M where
  state := id
  context := id
  intervention := id
  idle_law := rfl
  commutes := fun _ _ => rfl

def comp {M N P : ResponseModel.{u}} (g : CausalMap N P) (f : CausalMap M N) :
    CausalMap M P where
  state := g.state ∘ f.state
  context := g.context ∘ f.context
  intervention := g.intervention ∘ f.intervention
  idle_law := by dsimp; rw [f.idle_law, g.idle_law]
  commutes := by intro u i; dsimp; rw [f.commutes, g.commutes]

theorem ident_comp {M N : ResponseModel.{u}} (f : CausalMap M N) :
    comp (ident N) f = f := ext rfl rfl rfl
theorem comp_ident {M N : ResponseModel.{u}} (f : CausalMap M N) :
    comp f (ident M) = f := ext rfl rfl rfl
theorem assoc {M N P Q : ResponseModel.{u}}
    (h : CausalMap P Q) (g : CausalMap N P) (f : CausalMap M N) :
    comp (comp h g) f = comp h (comp g f) := ext rfl rfl rfl

def system : ArrowSystem ResponseModel.{u} ResponseModel.State where
  Hom := CausalMap
  map := CausalMap.state
  ident := ident
  comp := comp
  map_ident := fun _ => rfl
  map_comp := fun _ _ => rfl
  ident_comp := ident_comp
  comp_ident := comp_ident
  assoc := assoc
end CausalMap

def Onto {A B : Type u} (f : A → B) : Prop := ∀ b, ∃ a, f a = b
theorem onto_id (A : Type u) : Onto (id : A → A) := fun a => ⟨a, rfl⟩

theorem lens_get_onto {S V : Type u} (f : Lens S V) (s : S) : Onto f.get :=
  fun v => ⟨f.put s v, f.put_get s v⟩
theorem onto_comp {A B D : Type u} {f : A → B} {g : B → D}
    (hf : Onto f) (hg : Onto g) : Onto (g ∘ f) := by
  intro d
  obtain ⟨b, hb⟩ := hg d
  obtain ⟨a, ha⟩ := hf b
  exact ⟨a, by dsimp; rw [ha, hb]⟩

def CausalMap.OntoAll {M N : ResponseModel.{u}} (f : CausalMap M N) : Prop :=
  Onto f.state ∧ Onto f.context ∧ Onto f.intervention

theorem causal_ident_onto (M : ResponseModel.{u}) : (CausalMap.ident M).OntoAll :=
  ⟨onto_id M.State, onto_id M.Context, onto_id M.Intervention⟩

theorem causal_comp_onto {M N P : ResponseModel.{u}}
    (g : CausalMap N P) (f : CausalMap M N)
    (hg : g.OntoAll) (hf : f.OntoAll) : (CausalMap.comp g f).OntoAll := by
  exact ⟨onto_comp (f := f.state) (g := g.state) hf.1 hg.1,
    onto_comp (f := f.context) (g := g.context) hf.2.1 hg.2.1,
    onto_comp (f := f.intervention) (g := g.intervention) hf.2.2 hg.2.2⟩

end ApprehensionEnrichments
