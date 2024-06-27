import Mathlib
import Mathlib.Topology.Separation
import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] --[T2Space X]

--α^*
noncomputable section
variable (K:Compacts X)
variable (F:(Opens X)ᵒᵖ⥤ Ab)
variable (P:Opens X → Prop)-- true pour le alpha normal et IsCompact (closure U.carrier) pour la version relativement compacte

def KsubU : Set (Opens X) := fun U : Opens X ↦ K.carrier ⊆ U.carrier ∧ P U

def KsubU_cat : Type := FullSubcategory (KsubU K P)

/-instance : SetLike (KsubU_cat X K P) X where
  coe U:= U.obj.carrier

  coe_injective':= fun ⟨_ , _ ⟩ ⟨_, _⟩ h => by
    apply FullSubcategory.ext
    simp at h
    exact h-/


instance : Category (KsubU_cat K P) := FullSubcategory.category (KsubU K P)

def FU : (KsubU_cat K P)ᵒᵖ ⥤ Ab := (fullSubcategoryInclusion <| KsubU K P).op.comp  F

variable {K₁ K₂ : Compacts X} (f : K₁ ⟶ K₂)

def K₁subK₂subU : (KsubU_cat K₂ P) ⥤ (KsubU_cat K₁ P) where
  obj W := ⟨W.obj, Set.Subset.trans (leOfHom f) W.property.1, W.property.2⟩
  map {U V} F := homOfLE (leOfHom F)

def K₁subK₂natTrans : FU K₂ F P ⟶  (Functor.comp (K₁subK₂subU P f).op (FU K₁ F P)) where
  app W := 𝟙 _

def AlphaUpStarF :(Compacts X)ᵒᵖ ⥤ Ab  where
  obj K := colimit (FU K.unop F P)
  map f:= colimMap (K₁subK₂natTrans F P f.unop) ≫ (colimit.pre (FU _ F P) (K₁subK₂subU P f.unop).op)
  map_id := by aesop (add safe apply colimit.hom_ext)
  map_comp := by aesop (add safe apply colimit.hom_ext)

variable {F1 F2 : (Opens X)ᵒᵖ ⥤ Ab} (τ : F1 ⟶ F2)

def τres : FU K F1 P ⟶ FU K F2 P where
  app U:= τ.app (op (U.unop.obj))
  naturality := by
    unfold FU
    simp [τ.naturality]

def AlphaUpStarTau : AlphaUpStarF F1 P ⟶ AlphaUpStarF F2 P where
  app K := colimMap (τres K.unop P τ)
  naturality := by
    intro _ _ _
    apply colimit.hom_ext
    intro _
    unfold AlphaUpStarF
    simp
    rfl

def AlphaUpStarP :((Opens X)ᵒᵖ ⥤ Ab) ⥤ ((Compacts X)ᵒᵖ ⥤ Ab) where
  obj F:= AlphaUpStarF F P
  map τ := AlphaUpStarTau P τ
  map_id:= by
    intro F
    apply NatTrans.ext
    apply funext
    intro _
    apply colimit.hom_ext
    intro U
    unfold AlphaUpStarTau AlphaUpStarF τres
    simp
    rw [@Category.id_comp _ _ (F.obj { unop := U.unop.obj }) _ _]
  map_comp:= by
    intro _ _ _ _ _
    apply NatTrans.ext
    apply funext
    intro _
    apply colimit.hom_ext
    intro _
    unfold AlphaUpStarTau τres
    simp

variable (X)

def trueCond: Opens X → Prop := (fun (_:Opens X) => true)

def AlphaUpStar : ((Opens X)ᵒᵖ ⥤ Ab)⥤ ((Compacts X)ᵒᵖ ⥤ Ab) := AlphaUpStarP (trueCond X)

end

noncomputable section
--α_*
variable (U:Opens X) (G:(Compacts X)ᵒᵖ ⥤ Ab)

def UsupK : Set (Compacts X) := fun (K:Compacts X) => (K.carrier ⊆ U.carrier) --∧ IsCompact (closure U.carrier) peut être?

def UsupK_cat : Type := FullSubcategory (UsupK U)

instance : Category (UsupK_cat U) := FullSubcategory.category (UsupK U)

def GK : (UsupK_cat U)ᵒᵖ ⥤ Ab := Functor.comp (fullSubcategoryInclusion (UsupK U)).op  G

variable {U1 U2 : Opens X} (f : U1 ⟶ U2)

def U2supU1supK : (UsupK_cat U1) ⥤ (UsupK_cat U2) where
  obj W:=(⟨W.obj,Set.Subset.trans W.property (leOfHom f)⟩ : UsupK_cat U2)
  map := by
    intro _ _ F
    exact homOfLE (leOfHom F)

def U2supU1natTrans : (GK U1 G) ⟶  (Functor.comp (U2supU1supK f).op (GK U2 G)) where
  app W := 𝟙 _

def AlphaDownStarG :(Opens X)ᵒᵖ ⥤ Ab  where
  obj U := limit (GK U.unop G)
  map f:= (limit.pre (GK G) (U2supU1supK f.unop).op) ≫ limMap (U2supU1natTrans G f.unop)
  map_id := by
    intro _
    apply limit.hom_ext
    simp
    intro _
    rfl
  map_comp := by
    intro _ _ _ _ _
    simp
    apply limit.hom_ext
    intro _
    simp
    rfl

variable (G1:(Compacts X)ᵒᵖ⥤ Ab) (G2:(Compacts X)ᵒᵖ⥤ Ab) (σ :G1 ⟶ G2)

def σres :(GK X U G1)⟶ (GK X U G2) where
  app K:= σ.app (op (K.unop.obj))
  naturality := by
    unfold GK
    simp [σ.naturality]

def AlphaDownStarSigma : (AlphaDownStarG X G1) ⟶ (AlphaDownStarG X G2) where
  app U := limMap (σres X U.unop G1 G2 σ )
  naturality := by
    intro _ _ _
    apply limit.hom_ext
    intro _
    unfold AlphaDownStarG
    simp
    rfl


def AlphaDownStar :((Compacts X)ᵒᵖ ⥤ Ab)⥤ ((Opens X)ᵒᵖ ⥤ Ab) where
  obj G:= AlphaDownStarG X G
  map σ := AlphaDownStarSigma X _ _ σ
  map_id:= by
    intro G
    apply NatTrans.ext
    apply funext
    intro _
    apply limit.hom_ext
    intro U
    unfold AlphaDownStarSigma σres
    simp
    rw [@Category.comp_id _ _ _ (G.obj { unop := U.unop.obj }) _]
  map_comp:= by
    intro _ _ _ _ _
    apply NatTrans.ext
    apply funext
    intro _
    apply limit.hom_ext
    intro _
    unfold AlphaDownStarSigma σres
    simp
end

--Adjunction

variable (F:(Opens X)ᵒᵖ⥤ Ab) (G:(Compacts X)ᵒᵖ ⥤ Ab) (τ:(AlphaUpStar X).obj F⟶ G) (σ :F⟶ (AlphaDownStar X).obj G)
variable (K:Compacts X) (U:Opens X)

noncomputable section


def ConeFtoAG_NT: (Functor.const (UsupK_cat X U)ᵒᵖ).obj (F.obj { unop := U }) ⟶ GK X U G where
  app L := by
    unfold GK
    simp
    apply CategoryStruct.comp _ (τ.app _ )
    apply CategoryStruct.comp _
    apply colimit.ι
    apply op
    exact ⟨U,L.unop.property,rfl⟩
    exact 𝟙 _

  naturality := by
    intro K L f
    unfold GK
    simp
    rw [← (τ.naturality _)]
    unfold AlphaUpStar AlphaUpStarP AlphaUpStarF K₁subK₂natTrans K₁subK₂subU
    simp

def ConeFtoAG :Cone (GK X U G) where
  pt:= F.obj {unop:= U}
  π:=(ConeFtoAG_NT X F G τ U)

def FtoAG : ( F ⟶ (AlphaDownStar X).obj G) where
  app U:= limit.lift _ (ConeFtoAG X F G τ U.unop)
  naturality := by
    intro U V f
    apply limit.hom_ext
    intro K
    unfold AlphaDownStar AlphaDownStarG  U2supU1natTrans U2supU1supK ConeFtoAG ConeFtoAG_NT
    simp

    rw [@Category.comp_id _ _ _ ((GK X V.unop G).obj K) _,← Category.assoc,← colimit.w_assoc]
    rfl

def CoconeAFtoG_NT: FU X K F P ⟶ (Functor.const (KsubU_cat X K P)ᵒᵖ).obj (G.obj { unop := K })  where
  app W := by
    apply CategoryStruct.comp (σ.app _ )
    apply CategoryStruct.comp
    apply limit.π
    apply op
    simp
    exact ⟨_,W.unop.property.1⟩
    exact 𝟙 _
  naturality := by
    intro K L f
    unfold FU
    simp
    unfold AlphaDownStar AlphaDownStarG U2supU1natTrans U2supU1supK
    simp
    rfl

def CoconeAFtoG :Cocone (FU X K F P) where
  pt:= G.obj {unop:= K}
  ι :=(CoconeAFtoG_NT X F G σ K)

def AFtoG : ( (AlphaUpStar X).obj F ⟶  G) where
  app K:= colimit.desc _ (CoconeAFtoG X F G σ K.unop)
  naturality := by
    intro K L f
    apply colimit.hom_ext
    intro V
    unfold AlphaUpStar AlphaUpStarP AlphaUpStarF  K₁subK₂natTrans K₁subK₂subU CoconeAFtoG CoconeAFtoG_NT
    simp
    rw [← limit.w _ _]
    rfl

def homEquiv: ((AlphaUpStar X ).obj F ⟶ G) ≃ ( F ⟶ (AlphaDownStar X).obj G) where
  toFun := fun τ => (FtoAG X F G τ )
  invFun := fun σ => (AFtoG X F G σ)
  left_inv := by
    intro σ
    apply NatTrans.ext
    apply funext
    intro K
    apply colimit.hom_ext
    intro U
    unfold AFtoG CoconeAFtoG CoconeAFtoG_NT FtoAG ConeFtoAG ConeFtoAG_NT
    simp
    rfl
  right_inv := by
    intro τ
    apply NatTrans.ext
    apply funext
    intro K
    apply limit.hom_ext
    intro U
    simp
    unfold FtoAG ConeFtoAG ConeFtoAG_NT AFtoG CoconeAFtoG CoconeAFtoG_NT
    simp
    rfl

def adjthm : Adjunction.CoreHomEquiv (AlphaUpStar X) (AlphaDownStar X) where
homEquiv := (homEquiv X)
homEquiv_naturality_left_symm:= by
  intro _ _ _ _ _
  apply NatTrans.ext
  apply funext
  intro _
  apply colimit.hom_ext
  intro _
  unfold homEquiv AlphaUpStar AlphaUpStarP AlphaUpStarTau AFtoG CoconeAFtoG CoconeAFtoG_NT τres
  simp
homEquiv_naturality_right:= by
  intro F G1 G2 τ σ
  apply NatTrans.ext
  apply funext
  intro U
  apply limit.hom_ext
  intro K
  unfold homEquiv AlphaDownStar AlphaDownStarSigma FtoAG ConeFtoAG ConeFtoAG_NT σres
  simp

def AdjAlphaStar : (AlphaUpStar X ) ⊣ (AlphaDownStar X ) := Adjunction.mkOfHomEquiv (adjthm X)
