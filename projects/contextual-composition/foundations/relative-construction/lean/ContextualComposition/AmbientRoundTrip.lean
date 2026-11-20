module
public import ContextualComposition.AmbientDescentRecognition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientRoundTrip
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite NativeCleavage FibreValue TelescopeSquares
open ContextadModification ContextadAmbientPayload ContextadPayloadModification AmbientDescentRecognition WordTrace
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{v} B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u})
variable (F : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)) (h : F ⋙ proj Z = proj Y) (p : Pres F (proj Y) (proj Z))
theorem encodeDecode : totalStrong (decodedStrong Y Z F h p) = F := by
  apply Edge.functor_ext
  intro z
  let a := decodedStrong Y Z F h p
  let A := grade _ _ z.src
  let E := grade _ _ z.dst
  let g := gradeMap z.hom
  let w := payloadMap z.hom
  let x := payload _ _ z.dst
  let k := (a.app ⟨op A⟩).toFunctor.map w
  let l := (ContextadTotal.valueSquare Y Z F h p g).hom.app x
  let m := FibreValue.arrow Z g ((a.app ⟨op E⟩).toFunctor.obj x)
  have left := (ContextadCartesian.factorTotal Z (𝟭 B) ((totalStrong a).map z.hom)).symm
  change (totalStrong a).map z.hom = (incl Z A).map (k ≫ l) ≫ m at left
  rw [Functor.map_comp,Category.assoc] at left
  have right := ContextadCartesian.factorTotal Y (𝟭 B) z.hom
  let j := (incl Y A).map w
  let t := FibreValue.arrow Y g x
  change j ≫ t = z.hom at right
  have v : Aligned ((incl Z A).map k) (F.map j) := NativeCube.functorAlign (ContextadRecognition.genericIncl Y Z A F h) w
  have whole := (NativeCube.ofEq left).trans ((v.comp (decodedFac Y Z h p g x)).trans
    (NativeCube.ofEq ((F.map_comp j t).symm.trans (congrArg F.map right))))
  exact Edge.eq_of whole.src whole.dst (ContextadUnitTotal.alignedHEq whole)
variable {Y Z}
noncomputable abbrev compAt (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (A : B) := (a.app ⟨op A⟩).toFunctor
theorem alignOf {C : Type*} [Category* C] {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (p : x = x') (q : y = y') (h : HEq f g) : Aligned f g := by subst x'; subst y'; exact NativeCube.ofEq (eq_of_heq h)
theorem strongIncl (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (A : B) :
    compAt a A ⋙ incl Z A = incl Y A ⋙ totalStrong a := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    apply (homEquiv _ _).injective
    refine Sigma.ext rfl ?_
    have left := embed_payload Z ((compAt a A).map f)
    have right := embed_payload Y f
    change HEq _ ((compAt a A).map (payloadMap ((incl Y A).map f)) ≫ (a.naturality (𝟙 A).op.toLoc).hom.toNatTrans.app y)
    apply left.trans
    have s := StrongTrans.naturality_id a ⟨op A⟩
    have n := congrArg (fun q => q.toNatTrans.app y) s
    simp [Functor.toPseudofunctor'_mapId,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app] at n
    have pn : Pure ((a.naturality (𝟙 A).op.toLoc).hom.toNatTrans.app y) := pureCancel ⟨_,n⟩ ⟨_,rfl⟩
    have pr := (alignOf rfl (Functor.congr_obj (congrArg Cat.Hom.toFunctor (Y.map_id _)) y) right).map (compAt a A)
    obtain ⟨q,hq⟩ := pn
    rw [hq]
    exact ContextadUnitTotal.alignedHEq ((Aligned.trailing _ q).trans pr).symm

theorem payloadHEq {x y x' y' : Total Z (𝟭 B)} {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g) :
    HEq (payloadMap f) (payloadMap g) := by
  obtain ⟨rfl,rfl,h⟩ := h; simp at h; subst g; rfl
theorem onLift (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') {A E : B} (f : A ⟶ E) (x : Y.obj (op E)) :
    payloadMap ((totalStrong a).map (FibreValue.arrow Y f x)) = (a.naturality f.op.toLoc).hom.toNatTrans.app x := by
  change (compAt a A).map (𝟙 _) ≫ _ = _
  rw [Functor.map_id,Category.id_comp]
  rfl
theorem strongExt {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} (h : a.app = b.app)
    (k : ∀ {A E : B} (f : A ⟶ E) (x : Y.obj (op E)),
      HEq ((a.naturality f.op.toLoc).hom.toNatTrans.app x) ((b.naturality f.op.toLoc).hom.toNatTrans.app x)) : a = b := by
  obtain ⟨ap,n,hn,hi,hc⟩ := a
  obtain ⟨bp,m,gn,gi,gc⟩ := b
  change ap = bp at h; subst bp
  have q : @n = @m := by
    funext X T f
    apply Iso.ext
    apply Cat.Hom₂.ext
    ext x : 2
    exact eq_of_heq (k f.as.unop x)
  cases q; rfl
theorem encodeInjective : Function.Injective (totalStrong (Y := Y) (Z := Z)) := by
  intro a b h
  apply strongExt
  · funext A
    apply congrArg Functor.toCatHom
    apply ContextadFinal.cancelIncl Z A.as.unop
    exact (strongIncl a _).trans ((congrArg (incl Y A.as.unop ⋙ ·) h).trans (strongIncl b _).symm)
  · intro A E f x
    rw [← onLift a f x,← onLift b f x]
    exact payloadHEq (NativeCube.functorAlign h (FibreValue.arrow Y f x))
theorem decodeEncode (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') :
    decodedStrong Y Z (totalStrong a) (strongOver a) (strongCart a) = a :=
  encodeInjective (encodeDecode Y Z _ _ _)
end ContextualComposition.GrothendieckStep.AmbientRoundTrip
