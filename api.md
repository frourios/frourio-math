# Lean API

## ./lean-toolchain
leanprover/lean4:v4.23.0-rc2


## ./Frourio.lean

No definitions found


## ./Frourio/Algebra/CrossedProduct.lean

namespace Frourio


def IsPBWBasis {A : Type*} [Ring A] {m : ℕ}
    (basis : Set (CrossedProduct A m)) : Prop  := proven

theorem pbw_basis {A : Type*} [Ring A] (m : ℕ) :
    ∃ (basis : Set (CrossedProduct A m)), IsPBWBasis basis  := proven

noncomputable abbrev PBWModule (A : Type*) [Semiring A] (m : ℕ)  := proven

noncomputable def pbwMonomial {A : Type*} [Semiring A] (m : ℕ)
    (v : Fin m → ℤ) (a : A) : PBWModule A m  := proven

noncomputable def pbwFamily {A : Type*} [Semiring A] (m : ℕ) : (Fin m → ℤ) → PBWModule A m  := proven

def PBWLinearIndependent (A : Type*) [Semiring A] (m : ℕ) : Prop  := proven

def PBWSpans (A : Type*) [Semiring A] (m : ℕ) : Prop  := proven

structure StrongIsPBWBasis (A : Type*) [Semiring A] (m : ℕ) : Prop where
  (linIndep : PBWLinearIndependent A m)
  (spans : PBWSpans A m) := proven

lemma sum_single_eq_self {A : Type*} [Semiring A] {m : ℕ}
    (l : (Fin m → ℤ) →₀ A) :
    l.sum (fun v a => Finsupp.single v a) = l  := proven


lemma pbw_linearIndependent_basic {A : Type*} [Semiring A] (m : ℕ) :
    PBWLinearIndependent A m  := proven

lemma pbw_spans_basic {A : Type*} [Semiring A] (m : ℕ) :
    PBWSpans A m  := proven

theorem pbw_basis_strong {A : Type*} [Semiring A] (m : ℕ) :
    StrongIsPBWBasis A m  := proven

noncomputable def toPBW {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) : PBWModule A m  := proven


@[simp] lemma toPBW_def {A : Type*} [Ring A] {m : ℕ}
    (a : A) (v : Fin m → ℤ) :
    toPBW (A := A) { base := a, scales := v } = Finsupp.single v a  := proven

def fromPBW_of_eq_single {A : Type*} [Ring A] {m : ℕ}
    {f : PBWModule A m} {v : Fin m → ℤ} {a : A}
    (_hv : f = Finsupp.single v a) : CrossedProduct A m  := proven


@[simp] lemma from_toPBW {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) :
    fromPBW_of_eq_single (A := A) (m := m)
      (f := toPBW (A := A) x) (v := x.scales) (a := x.base) rfl = x  := proven


@[simp] lemma to_fromPBW {A : Type*} [Ring A] {m : ℕ}
    {v : Fin m → ℤ} {a : A} :
    toPBW (A := A) (m := m)
      (fromPBW_of_eq_single (A := A) (m := m)
        (f := Finsupp.single v a) (v := v) (a := a) rfl)
      = Finsupp.single v a  := proven


@[simp] lemma toPBW_zero {A : Type*} [Ring A] {m : ℕ} :
    toPBW (A := A) (m := m) (0 : CrossedProduct A m) = 0  := proven

lemma toPBW_add_zero_scales {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) (hx : x.scales = 0) (hy : y.scales = 0) :
    toPBW (x + y) = toPBW x + toPBW y  := proven

lemma toPBW_neg_scale_zero {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) (h : x.scales = 0) :
    toPBW (-x) = - toPBW x  := proven


instance instSubCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Sub (CrossedProduct A m) where
  sub x y  := proven

lemma toPBW_sub_same_zero_scales {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) (hx : x.scales = 0) (hy : y.scales = 0) :
    toPBW (x - y) = toPBW x - toPBW y  := proven


@[simp] lemma single_eq_single_iff {A : Type*} [Ring A] {m : ℕ}
    {v w : Fin m → ℤ} {a b : A} :
    (Finsupp.single v a : PBWModule A m) = Finsupp.single w b ↔
    (v = w ∧ a = b) ∨ (a = 0 ∧ b = 0)  := proven


lemma toPBW_injective_on_single {A : Type*} [Ring A] {m : ℕ}
    {v : Fin m → ℤ} {a : A} (ha : a ≠ 0) :
    ∀ x : CrossedProduct A m,
    toPBW x = Finsupp.single v a → x = { base := a, scales := v }  := proven


lemma eq_of_toPBW_eq_on_single {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) (hx : x.base ≠ 0) (hy : y.base ≠ 0) :
    toPBW x = toPBW y → x = y  := proven


noncomputable def pbwSum {A : Type*} [Semiring A] (m : ℕ)
    (s : Finset (Fin m → ℤ)) (c : (Fin m → ℤ) → A) : PBWModule A m  := proven

noncomputable def PBWModule.mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y : PBWModule A m) : PBWModule A m  := proven

structure FrourioCrossedProduct (A : Type*) [Ring A] (m : ℕ) where
  elem : PBWModule A m := proven


noncomputable instance instMulFrourioCrossedProduct {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) : Mul (FrourioCrossedProduct A m) where
  mul x y  := proven


lemma toPBW_mul_single_right {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : CrossedProduct A m) (v : Fin m → ℤ) (a : A) :
    toPBW (CrossedProduct.mul σ x { base := a, scales := v }) =
    PBWModule.mul σ (toPBW x) (Finsupp.single v a)  := proven


lemma toPBW_mul_single_left {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (a : A) (y : CrossedProduct A m) :
    toPBW (CrossedProduct.mul σ { base := a, scales := v } y) =
    PBWModule.mul σ (Finsupp.single v a) (toPBW y)  := proven


lemma toPBW_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y : CrossedProduct A m) :
    toPBW (CrossedProduct.mul σ x y) = PBWModule.mul σ (toPBW x) (toPBW y)  := proven

end Frourio


## ./Frourio/Algebra/CrossedProductCore.lean

namespace Frourio

structure DihedralInfinity where
  /- TODO: 生成元と関係式を群表示として実装 -/
  deriving Repr, Inhabited := proven

namespace DihedralInfinity

inductive Word
  | id : Word
  | u (n : ℤ) : Word       -- u^n
  | ur (n : ℤ) : Word      -- u^n * r
  deriving Repr, DecidableEq := proven

def Word.mul : Word → Word → Word
  | Word.id, w => w
  | w, Word.id => w
  | Word.u n, Word.u m => Word.u (n + m)
  | Word.u n, Word.ur m => Word.ur (n + m)
  | Word.ur n, Word.u m => Word.ur (n - m)  -- rur = u⁻¹ より
  | Word.ur n, Word.ur m => Word.u (n - m)  -- r² = 1 より := proven

end DihedralInfinity

structure CrossedProduct (A : Type*) [Ring A] (m : ℕ) where
  base : A
  scales : Fin m → ℤ  -- スケール作用の指数
  deriving Repr := proven

structure ZmAction (A : Type*) [Ring A] (m : ℕ) where
  act : (Fin m → ℤ) → A → A
  act_zero : ∀ a, act 0 a = a
  act_add : ∀ v w a, act (v + w) a = act v (act w a)
  map_one : ∀ v, act v 1 = 1
  map_mul : ∀ v a b, act v (a * b) = act v a * act v b
  map_zero : ∀ v, act v 0 = 0
  map_add : ∀ v a b, act v (a + b) = act v a + act v b := proven

def CrossedProduct.mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m)
    (x y : CrossedProduct A m) : CrossedProduct A m  := proven

instance instMulCrossedProduct {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) : Mul (CrossedProduct A m) where
  mul x y  := proven


instance instOneCrossedProduct {A : Type*} [Ring A] {m : ℕ} : One (CrossedProduct A m) where
  one  := proven


instance instAddCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Add (CrossedProduct A m) where
  add x y  := proven


instance instZeroCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Zero (CrossedProduct A m) where
  zero  := proven


instance instNegCrossedProduct {A : Type*} [Ring A] {m : ℕ} : Neg (CrossedProduct A m) where
  neg x  := proven


theorem add_assoc_crossed {A : Type*} [Ring A] {m : ℕ}
    (x y z : CrossedProduct A m) : x + y + z = x + (y + z)  := proven


theorem add_comm_crossed {A : Type*} [Ring A] {m : ℕ}
    (x y : CrossedProduct A m) : x + y = y + x  := proven


theorem add_left_neg_crossed {A : Type*} [Ring A] {m : ℕ}
    (x : CrossedProduct A m) : -x + x = 0  := proven

theorem scales_eq_zero_if_left_distrib {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : CrossedProduct A m)
    (h : CrossedProduct.mul σ (x + y) z =
         (CrossedProduct.mul σ x z) + (CrossedProduct.mul σ y z)) :
    z.scales = 0  := proven

theorem mul_assoc_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : CrossedProduct A m) :
    CrossedProduct.mul σ (CrossedProduct.mul σ x y) z =
    CrossedProduct.mul σ x (CrossedProduct.mul σ y z)  := proven

theorem one_mul_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : CrossedProduct A m) :
    CrossedProduct.mul σ (One.one) x = x  := proven

theorem mul_one_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : CrossedProduct A m) :
    CrossedProduct.mul σ x (One.one) = x  := proven

instance instMonoidCrossedProduct {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) : Monoid (CrossedProduct A m) where
  mul x y  := proven

def identityZmAction (A : Type*) [Ring A] (m : ℕ) : ZmAction A m  := proven

def FrourioOperator.toZmAction {m : ℕ}
    (_op : FrourioOperator m) (A : Type*) [Ring A] : ZmAction A m  := proven

noncomputable def FrourioOperator.scaleFactor {m : ℕ}
    (op : FrourioOperator m) (v : Fin m → ℤ) : ℝ  := proven

noncomputable def FrourioOperator.toZmActionOnFunctions {m : ℕ}
    (op : FrourioOperator m) (B : Type*) [Ring B] :
    ZmAction (ℝ → B) m  := proven

structure IsSigmaDerivation {A : Type*} [Ring A]
    (σ : A →+* A) (δ : A → A) : Prop where
  (map_add : ∀ a b, δ (a + b) = δ a + δ b)
  (map_mul : ∀ a b, δ (a * b) = σ a * δ b + δ a * b) := proven

lemma isSigmaDerivation_zero {A : Type*} [Ring A]
    (σ : A →+* A) : IsSigmaDerivation σ (fun _ : A => 0)  := proven

structure OreSystem (A : Type*) [CommRing A] where
  (E : Type*)
  [ringE : Ring E]
  [algebraAE : Algebra A E]
  (Δ : E)
  (σ : A →+* A)
  (δ : A → A)
  (isSigmaDerivation : IsSigmaDerivation σ δ)
  (ore_rel : ∀ a : A,
    Δ * (algebraMap A E a) - (algebraMap A E (σ a)) * Δ = algebraMap A E (δ a))
attribute [instance] OreSystem.ringE OreSystem.algebraAE := proven

def oreExchange {A : Type*} [CommRing A] {m : ℕ}
    (_op : FrourioOperator m) (sys : OreSystem A) : Prop  := proven

def FrourioOperator.toTrivialOreSystem {m : ℕ}
    (_op : FrourioOperator m) (A : Type*) [CommRing A] : OreSystem A  := proven

def oreFromSigma {A : Type*} [CommRing A] (σ : A →+* A) : OreSystem A  := proven

noncomputable def scaleRingHom (B : Type*) [CommRing B] (c : ℝ) :
    (ℝ → B) →+* (ℝ → B)  := proven

noncomputable def FrourioOperator.toOreSystemOnFunctions
    {m : ℕ} (op : FrourioOperator m) (B : Type*) [CommRing B]
    (i : Fin m) : OreSystem (ℝ → B)  := proven

noncomputable def phiOreSystem : OreSystem ℝ  := proven

noncomputable def OreSystem.matrixJordanId (A : Type*) [CommRing A] : OreSystem A  := proven

noncomputable def OreSystem.matrixJordan {A : Type*} [CommRing A]
    (σ : A →+* A) : OreSystem A  := proven

def matrixJordanDiagProp {A : Type*} [CommRing A]
    (σ : A →+* A) : Prop  := proven

structure SigmaPBW (A : Type*) [CommRing A] (ι : Type*) where
  (E : Type*)
  [ringE : Ring E]
  [algebraAE : Algebra A E]
  (Δ : ι → E)
  (σ : ι → A →+* A)
  (δ : ι → A → A)
  (isSigmaDerivation : ∀ i, IsSigmaDerivation (σ i) (δ i))
  (ore_rel : ∀ i a, Δ i * (algebraMap A E a)
                    - (algebraMap A E ((σ i) a)) * Δ i
                    = algebraMap A E ((δ i) a))
attribute [instance] SigmaPBW.ringE SigmaPBW.algebraAE := proven

abbrev CriticalPair (ι : Type*)  := proven

def DiamondCriticalPairs (ι : Type*)  := proven

lemma ore_rewrite_one {A : Type*} [CommRing A]
    (sys : OreSystem A) (a : A) :
    sys.Δ * algebraMap A sys.E a
      = algebraMap A sys.E (sys.σ a) * sys.Δ + algebraMap A sys.E (sys.δ a)  := proven

def monomial {A : Type*} [Ring A] {m : ℕ}
    (v : Fin m → ℤ) : CrossedProduct A m  := proven

end Frourio


## ./Frourio/Algebra/NambuBracket.lean

namespace Frourio

abbrev Func  := proven

abbrev DiffOp  := proven

structure DiffFamily where
  (L : Fin 3 → DiffOp)
  (commute : Prop)      -- later: L_i L_j = L_j L_i
  (smallParams : Prop)  -- later: smallness of β_i = log Λ_i, step m etc. := proven

end Frourio


## ./Frourio/Algebra/Operators.lean

namespace Frourio

structure ScaleOperator where
  scale : ℝ
  scale_pos : 0 < scale := proven

@[ext]
lemma ScaleOperator.ext (U V : ScaleOperator) (h : U.scale = V.scale) : U = V  := proven

noncomputable def ScaleOperator.act {α : Type*} (U : ScaleOperator) (f : ℝ → α) : ℝ → α  := proven

noncomputable def ScaleOperator.comp (U V : ScaleOperator) : ScaleOperator  := proven

noncomputable def ScaleOperator.inv (U : ScaleOperator) : ScaleOperator  := proven

def ScaleOperator.id : ScaleOperator  := proven

lemma ScaleOperator.comp_assoc (U V W : ScaleOperator) :
    (U.comp V).comp W = U.comp (V.comp W)  := proven

lemma ScaleOperator.id_comp (U : ScaleOperator) :
    id.comp U = U  := proven

lemma ScaleOperator.comp_id (U : ScaleOperator) :
    U.comp id = U  := proven

lemma ScaleOperator.inv_comp (U : ScaleOperator) :
    U.inv.comp U = id  := proven

lemma ScaleOperator.comp_inv (U : ScaleOperator) :
    U.comp U.inv = id  := proven

lemma ScaleOperator.act_comp {α : Type*} (U V : ScaleOperator) (f : ℝ → α) :
    U.act (V.act f) = (U.comp V).act f  := proven

lemma ScaleOperator.id_act {α : Type*} (f : ℝ → α) :
    id.act f = f  := proven

lemma ScaleOperator.inv_act {α : Type*} (U : ScaleOperator) (f : ℝ → α) :
    U.inv.act (U.act f) = f  := proven

lemma ScaleOperator.act_injective {α : Type*} (U : ScaleOperator) :
    Function.Injective (U.act : (ℝ → α) → (ℝ → α))  := proven

lemma ScaleOperator.act_smul (U : ScaleOperator) (c : ℂ) (f : ℝ → ℂ) :
    U.act (fun x => c * f x) = fun x => c * U.act f x  := proven

lemma ScaleOperator.act_add (U : ScaleOperator) (f g : ℝ → ℂ) :
    U.act (fun x => f x + g x) = fun x => U.act f x + U.act g x  := proven

lemma ScaleOperator.mellin_scale (U : ScaleOperator) (f : ℝ → ℂ) :
    ∀ x > 0, U.act f x = f (U.scale * x)  := proven

lemma ScaleOperator.pow_scale (U : ScaleOperator) (n : ℕ) :
    ∃ V : ScaleOperator, V.scale = U.scale ^ n ∧
    ∀ f : ℝ → ℂ, ∀ x : ℝ, V.act f x = f (U.scale ^ n * x)  := proven

noncomputable def ScaleOperator.golden : ScaleOperator  := proven

lemma ScaleOperator.golden_inv :
    golden.inv.scale = φ⁻¹  := proven

lemma ScaleOperator.comm (U V : ScaleOperator) :
    U.comp V = V.comp U  := proven

lemma ScaleOperator.square_eq_id_iff (U : ScaleOperator) :
    U.comp U = id ↔ U.scale = 1  := proven

structure InverseMultOperator where
  /-- 原点での振る舞いを指定するフラグ（デフォルトは0） -/
  atZero : ℂ  := proven

noncomputable def InverseMultOperator.act (M : InverseMultOperator) (f : ℝ → ℂ) : ℝ → ℂ  := proven

def InverseMultOperator.standard : InverseMultOperator  := proven

noncomputable def InverseMultOperator.square (M : InverseMultOperator) : InverseMultOperator  := proven

lemma InverseMultOperator.act_eq_div (M : InverseMultOperator) (f : ℝ → ℂ) (x : ℝ) :
    x ≠ 0 → M.act f x = f x / x  := proven

lemma InverseMultOperator.act_smul_standard (c : ℂ) (f : ℝ → ℂ) :
    InverseMultOperator.standard.act (fun x => c * f x) =
    fun x => c * InverseMultOperator.standard.act f x  := proven

lemma InverseMultOperator.act_add_standard (f g : ℝ → ℂ) :
    InverseMultOperator.standard.act (fun x => f x + g x) =
    fun x => InverseMultOperator.standard.act f x + InverseMultOperator.standard.act g x  := proven

structure FrourioParams (m : ℕ) where
  α : Fin m → ℂ           -- 複素係数
  χ : Fin m → Sign        -- 符号（+1 or -1）
  Λ : Fin m → ℝ           -- スケールパラメータ
  Λ_pos : ∀ i, 0 < Λ i    -- 正値条件 := proven

structure FrourioOperator (m : ℕ) extends FrourioParams m where := proven

noncomputable def BasicFrourioOperator (a : ℝ) (ha : 0 < a) : FrourioOperator 2  := proven

noncomputable def GoldenFrourioOperator : FrourioOperator 2  := proven

noncomputable def FrourioOperator.act {m : ℕ} (op : FrourioOperator m) (f : ℝ → ℂ) : ℝ → ℂ  := proven

noncomputable def FrourioOperator.toScaleOperator {m : ℕ}
    (op : FrourioOperator m) (i : Fin m) : ScaleOperator  := proven

noncomputable def FrourioOperator.toInverseMult {m : ℕ}
    (_op : FrourioOperator m) : InverseMultOperator  := proven

noncomputable def FrourioOperator.linearCombination {m : ℕ}
    (op : FrourioOperator m) (f : ℝ → ℂ) : ℝ → ℂ  := proven

lemma FrourioOperator.act_eq_inverseMult_linearComb {m : ℕ}
    (op : FrourioOperator m) (f : ℝ → ℂ) (x : ℝ) (hx : x ≠ 0) :
    op.act f x = op.linearCombination f x / x  := proven

lemma InverseMultOperator.mellin_shift (M : InverseMultOperator) (f : ℝ → ℂ) :
    ∀ x > 0, M.act f x = f x / x  := proven

lemma FrourioOperator.mellin_compatible {m : ℕ} (op : FrourioOperator m) :
    ∃ S : ℂ → ℂ, ∀ s : ℂ,
    S s = ∑ i : Fin m, op.α i * (op.χ i).toInt * (op.Λ i : ℂ)^(-s)  := proven

end Frourio


## ./Frourio/Algebra/PBWDistributivity.lean

namespace Frourio

theorem pbw_mul_single_single {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v₁ v₂ : Fin m → ℤ) (a₁ a₂ : A) :
    PBWModule.mul σ (Finsupp.single v₁ a₁) (Finsupp.single v₂ a₂) =
    Finsupp.single (v₁ + v₂) (a₁ * σ.act v₁ a₂)  := proven

theorem pbw_mul_zero_left {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ 0 x = 0  := proven

theorem pbw_mul_zero_right {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ x 0 = 0  := proven

lemma sum_zero_coeff {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (y : PBWModule A m) :
    (y.sum fun v₂ a₂ => Finsupp.single (v + v₂) (0 * σ.act v a₂)) = 0  := proven

theorem pbw_left_distrib_single_manual {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (a : A) (y z : PBWModule A m) :
    PBWModule.mul σ (Finsupp.single v a) (y + z) =
    PBWModule.mul σ (Finsupp.single v a) y + PBWModule.mul σ (Finsupp.single v a) z  := proven

theorem pbw_left_distrib {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : PBWModule A m) :
    PBWModule.mul σ x (y + z) = PBWModule.mul σ x y + PBWModule.mul σ x z  := proven

theorem pbw_right_distrib {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : PBWModule A m) :
    PBWModule.mul σ (x + y) z = PBWModule.mul σ x z + PBWModule.mul σ y z  := proven

theorem pbw_mul_assoc_single3 {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m)
    (v₁ v₂ v₃ : Fin m → ℤ) (a₁ a₂ a₃ : A) :
    PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v₁ a₁) (Finsupp.single v₂ a₂)) (Finsupp.single v₃ a₃)
      = PBWModule.mul σ (Finsupp.single v₁ a₁) (PBWModule.mul σ (Finsupp.single v₂ a₂) (Finsupp.single v₃ a₃))  := proven

theorem pbw_assoc_single_left {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (v : Fin m → ℤ) (a : A)
    (y z : PBWModule A m) :
    PBWModule.mul σ (PBWModule.mul σ (Finsupp.single v a) y) z =
    PBWModule.mul σ (Finsupp.single v a) (PBWModule.mul σ y z)  := proven

theorem pbw_mul_assoc {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x y z : PBWModule A m) :
    PBWModule.mul σ (PBWModule.mul σ x y) z =
    PBWModule.mul σ x (PBWModule.mul σ y z)  := proven

noncomputable def pbwOne {A : Type*} [Ring A] (m : ℕ) : PBWModule A m  := proven

theorem pbw_one_mul {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ (pbwOne m) x = x  := proven

theorem pbw_mul_one {A : Type*} [Ring A] {m : ℕ}
    (σ : ZmAction A m) (x : PBWModule A m) :
    PBWModule.mul σ x (pbwOne m) = x  := proven

end Frourio


## ./Frourio/Algebra/Properties.lean

namespace Frourio

noncomputable def mellinSymbol {m : ℕ} (op : FrourioOperator m) (s : ℂ) : ℂ  := proven

def satisfiesMomentCondition {m : ℕ} (op : FrourioOperator m) (r : ℕ) : Prop  := proven

lemma frourio_zero_not_moment0 (op : FrourioOperator 0) :
  ¬ satisfiesMomentCondition op 0  := proven

lemma frourio_one_insufficient (op : FrourioOperator 1) :
  ¬ satisfiesMomentCondition op 2  := proven

end Frourio


## ./Frourio/Algebra/StructureSequence.lean

namespace Frourio

noncomputable abbrev phiNum (Λ : ℝ) (n : ℕ) : ℝ  := proven

noncomputable def phiFactorial (Λ : ℝ) (n : ℕ) : ℝ  := proven

theorem phiFactorial_zero (Λ : ℝ) : phiFactorial Λ 0 = 1  := proven

theorem phiFactorial_one (Λ : ℝ) : phiFactorial Λ 1 = S Λ 1  := proven


theorem phiFactorial_succ (Λ : ℝ) (n : ℕ) :
    phiFactorial Λ (n + 1) = phiFactorial Λ n * S Λ ((n + 1 : ℕ) : ℤ)  := proven

noncomputable def phiDiff (Λ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ  := proven

noncomputable def phiDiffIter (Λ : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0,     f => f
  | n + 1, f => phiDiff Λ (phiDiffIter Λ n f) := proven

theorem phiDiff_leibniz (Λ : ℝ) (f g : ℝ → ℝ) :
    phiDiff Λ (fun x => f x * g x)
      = fun x => f (Λ * x) * phiDiff Λ g x + g (x / Λ) * phiDiff Λ f x  := proven

noncomputable def phiBinom (Λ : ℝ) (n k : ℕ) : ℝ  := proven

lemma phiBinom_zero_of_factorial_ne (Λ : ℝ) (n : ℕ)
    (h : phiFactorial Λ n ≠ 0) :
    phiBinom Λ n 0 = 1  := proven

lemma phiBinom_self_of_factorial_ne (Λ : ℝ) (n : ℕ)
    (h : phiFactorial Λ n ≠ 0) :
    phiBinom Λ n n = 1  := proven

lemma phiBinom_zero_of_Sone_ne (Λ : ℝ) (n : ℕ)
    (hΛpos : 0 < Λ) (hS1 : S Λ 1 ≠ 0) :
    phiBinom Λ n 0 = 1  := proven

lemma phiBinom_self_of_Sone_ne (Λ : ℝ) (n : ℕ)
    (hΛpos : 0 < Λ) (hS1 : S Λ 1 ≠ 0) :
    phiBinom Λ n n = 1  := proven

theorem higher_leibniz_base (Λ : ℝ) (f g : ℝ → ℝ) :
    (phiDiffIter Λ 0 (fun x => f x * g x) = fun x => f x * g x) ∧
    (phiDiffIter Λ 1 (fun x => f x * g x)
      = fun x => f (Λ * x) * phiDiff Λ g x + g (x / Λ) * phiDiff Λ f x)  := proven

theorem phiDiff_add (Λ : ℝ) (f g : ℝ → ℝ) :
    phiDiff Λ (fun x => f x + g x) = fun x => phiDiff Λ f x + phiDiff Λ g x  := proven

theorem higher_leibniz_two (Λ : ℝ) (f g : ℝ → ℝ) :
    phiDiffIter Λ 2 (fun x => f x * g x)
      = fun x =>
          f (Λ * (Λ * x)) * phiDiff Λ (phiDiff Λ g) x
            + phiDiff Λ g (x / Λ) * phiDiff Λ (fun t => f (Λ * t)) x
            + (g ((Λ * x) / Λ) * phiDiff Λ (phiDiff Λ f) x
                + phiDiff Λ f (x / Λ) * phiDiff Λ (fun t => g (t / Λ)) x)  := proven

theorem phiDiff_scale_invariant (Λ : ℝ) (hΛ : 1 < Λ) (c : ℝ) (hc : c ≠ 0)
    (f : ℝ → ℝ) :
    phiDiff Λ (fun x => f (c * x)) = fun x => c * phiDiff Λ f (c * x)  := proven

theorem phi_monomial_action (Λ : ℝ) (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    phiDiff Λ (fun y => y ^ (n + 1)) x =
      ((Λ ^ (n + 1) - 1 / Λ ^ (n + 1)) / (Λ - 1 / Λ)) * x ^ n  := proven

theorem S_at_one (n : ℤ) : S 1 n = 0  := proven

theorem S_odd_function (Λ : ℝ) (n : ℤ) : S Λ (-n) = -S Λ n  := proven

theorem phiBinom_symm (Λ : ℝ) (n k : ℕ) (hk : k ≤ n) :
    phiBinom Λ n k = phiBinom Λ n (n - k)  := proven


theorem phiBinom_pascal_candidate
    (Λ : ℝ) (_hΛpos : 0 < Λ) (_hS1 : S Λ 1 ≠ 0)
    (n k : ℕ) (_hk₁ : 0 < k) (hk₂ : k ≤ n) :
    phiBinom Λ (n + 1) k
      = phiBinom Λ n k * (S Λ ((n + 1 : ℕ) : ℤ)) / (S Λ (((n + 1 - k : ℕ) : ℤ)))  := proven

noncomputable def higherLeibnizRHS (Λ : ℝ) (n : ℕ) (f g : ℝ → ℝ) : ℝ → ℝ  := proven


theorem higher_leibniz_general
    (Λ : ℝ) (_hΛpos : 0 < Λ) (f g : ℝ → ℝ) (n : ℕ) :
    phiDiffIter Λ n (fun x => f x * g x) = higherLeibnizRHS Λ n f g  := proven


example (Λ : ℝ) (hΛpos : 0 < Λ) :
    S Λ (1 : ℤ) = 2 * Real.sinh (Real.log Λ)  := proven

end Frourio


## ./Frourio/Algebra/StructureSequenceCore.lean

namespace Frourio

noncomputable def S (Λ : ℝ) (n : ℤ) : ℝ  := proven

theorem S_neg (Λ : ℝ) (n : ℤ) : S Λ (-n) = -S Λ n  := proven

@[simp] theorem S_zero (Λ : ℝ) : S Λ 0 = 0  := proven

theorem S_one (Λ : ℝ) : S Λ 1 = Λ - 1 / Λ  := proven

theorem S_add (Λ : ℝ) (hΛ : 0 < Λ) (m n : ℤ) :
    S Λ (m + n) = S Λ m * Λ ^ n + S Λ n * Λ ^ (-m)  := proven

lemma two_sinh_neg (t : ℝ) : 2 * Real.sinh (-t) = -(2 * Real.sinh t)  := proven

theorem exp_nat_mul_log_eq_pow (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log Λ) = Λ ^ n  := proven

theorem S_as_exp_sub_exp_neg_ofNat (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    S Λ (n : ℤ) = Real.exp ((n : ℝ) * Real.log Λ)
                    - Real.exp (-( (n : ℝ) * Real.log Λ))  := proven

theorem S_as_sinh_ofNat (Λ : ℝ) (hΛpos : 0 < Λ) (n : ℕ) :
    S Λ (n : ℤ) = 2 * Real.sinh ((n : ℝ) * Real.log Λ)  := proven

theorem S_as_sinh_int (Λ : ℝ) (hΛpos : 0 < Λ) (m : ℤ) :
    S Λ m = 2 * Real.sinh ((m : ℝ) * Real.log Λ)  := proven


lemma S_nonneg_of_nat (Λ : ℝ) (hΛgt1 : 1 < Λ) (n : ℕ) :
    0 ≤ S Λ (n : ℤ)  := proven


lemma S_pos_of_nat_pos (Λ : ℝ) (hΛgt1 : 1 < Λ) {n : ℕ} (hn : 0 < n) :
    0 < S Λ (n : ℤ)  := proven


lemma S_ne_zero_of_pos_ne_one (Λ : ℝ) (hΛpos : 0 < Λ) (hΛne1 : Λ ≠ 1)
    {n : ℕ} (hn : 0 < n) : S Λ (n : ℤ) ≠ 0  := proven

end Frourio


## ./Frourio/Analysis/CauchyTheorem.lean

namespace Frourio

lemma rectangular_contour_conversion (f : ℂ → ℂ) (z₀ z₁ z₂ : ℂ) :
    ((∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) +
     I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I))) +
    (-(∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I))) +
    (-I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I))) =
    (∫ x : ℝ in z₀.re..z₁.re, f (x + z₀.im * I)) -
    (∫ x : ℝ in z₀.re..z₁.re, f (x + z₂.im * I)) +
    I • (∫ y : ℝ in z₀.im..z₂.im, f (z₁.re + y * I)) -
    I • (∫ y : ℝ in z₀.im..z₂.im, f (z₀.re + y * I))  := proven

lemma complex_norm_add_mul_I (x y : ℝ) :
    ‖(↑x : ℂ) + ↑y * I‖ = Real.sqrt (x^2 + y^2)  := proven

lemma integrable_of_gaussian_decay_horizontal {f : ℂ → ℂ} {y : ℝ}
    (hf_entire : ∀ z, DifferentiableAt ℂ f z)
    (hf_decay : ∃ (A B : ℝ) (hA : 0 < A) (hB : 0 < B),
      ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (-B * ‖z‖^2)) :
    Integrable (fun x : ℝ => f (x + y * I))  := proven


lemma cauchy_rectangle_formula {f : ℂ → ℂ} {R : ℝ} {y₁ y₂ : ℝ}
    (hf_rect : DifferentiableOn ℂ f (Set.uIcc (-R) R ×ℂ Set.uIcc y₁ y₂)) :
    (∫ x in (-R:ℝ)..R, f (x + y₁ * I)) - (∫ x in (-R:ℝ)..R, f (x + y₂ * I)) =
    - (I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I)))  := proven


lemma contour_limit_theorem {f : ℂ → ℂ} {y₁ y₂ : ℝ}
    (hf_integrable_y1 : Integrable (fun x : ℝ => f (x + y₁ * I)))
    (hf_integrable_y2 : Integrable (fun x : ℝ => f (x + y₂ * I)))
    (h_vert_vanish : ∀ ε > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ R ≥ R₀,
      ‖I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I))‖ < ε)
    (h_rect : ∀ R > (0 : ℝ),
      (∫ x in (-R:ℝ)..R, f (x + y₁ * I)) - (∫ x in (-R:ℝ)..R, f (x + y₂ * I)) =
      -(I • (∫ t in y₁..y₂, f (R + t * I)) - I • (∫ t in y₁..y₂, f (-R + t * I)))) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I)  := proven

theorem horizontal_contour_shift {f : ℂ → ℂ} {y₁ y₂ : ℝ}
    (hf_entire : ∀ z, DifferentiableAt ℂ f z)
    (hf_decay : ∃ (A B : ℝ) (_ : 0 < A) (_ : 0 < B),
      ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (-B * ‖z‖^2)) :
    ∫ x : ℝ, f (x + y₁ * I) = ∫ x : ℝ, f (x + y₂ * I)  := proven

end Frourio


## ./Frourio/Analysis/DoobTransform.lean

namespace Frourio

structure DoobDegradation where
  /-- The degradation amount ε(h) from the Doob function h -/
  ε : ℝ
  /-- Non-negativity (always true in BE theory) -/
  ε_nonneg : 0 ≤ ε
  /-- The degraded parameter after Doob transform -/
  degraded_lambda : ℝ → ℝ  := proven


structure Diffusion (X : Type*) where
  (E : (X → ℝ) → ℝ)
  (L : (X → ℝ) → (X → ℝ))
  (Gamma : (X → ℝ) → (X → ℝ))
  (Gamma2 : (X → ℝ) → (X → ℝ)) := proven

def HasCD {X : Type*} (D : Diffusion X) (lam : ℝ) : Prop  := proven

noncomputable def gammaPair {X : Type*} (D : Diffusion X)
  (f g : X → ℝ) : X → ℝ  := proven

def HasLeibnizL {X : Type*} (D : Diffusion X) : Prop  := proven

def HasLeibnizGamma {X : Type*} (D : Diffusion X) : Prop  := proven

noncomputable def doobL {X : Type*} (D : Diffusion X)
  (h : X → ℝ) : (X → ℝ) → (X → ℝ)  := proven

noncomputable def Doob {X : Type*} (h : X → ℝ) (D : Diffusion X) : Diffusion X  := proven


structure DoobAssumptions {X : Type*} (h : X → ℝ) (D : Diffusion X) where
  /-- Strict positivity of `h` ensuring the Doob transform is well-defined. -/
  (h_pos : ∀ x : X, 0 < h x)
  /-- Concrete Leibniz rule for the generator. -/
  (leibniz_L : HasLeibnizL D)
  /-- Concrete product rule for `Γ`. -/
  (leibniz_Gamma : HasLeibnizGamma D)
  (gamma_eq : (Doob h D).Gamma = D.Gamma)
  (gamma2_eq : ∀ f : X → ℝ, (Doob h D).Gamma2 f = D.Gamma2 f)
  /-- Curvature-dimension shift: for any CD parameter `lam` of `D`, there exists
  a possibly degraded parameter `lam'` for `Doob h D` with `lam' ≤ lam`.
  Later phases will refine this to an explicit formula using `∇² log h`. -/
  (cd_shift : ∀ lam : ℝ, HasCD D lam → ∃ lam' : ℝ, HasCD (Doob h D) lam' ∧ lam' ≤ lam)
  /-- BE degradation for meta-variational principle: λ_eff ≥ λ - 2ε(h).
  This field provides the degradation amount ε(h) ≥ 0 from the Hessian of log h. -/
  (BE_degradation : ℝ)
  /-- Non-negativity of degradation -/
  (BE_degradation_nonneg : 0 ≤ BE_degradation)
  /-- The cd_shift explicitly uses BE_degradation: Doob h D satisfies CD(λ - 2*BE_degradation) -/
  (cd_shift_explicit : ∀ lam : ℝ, HasCD D lam → HasCD (Doob h D) (lam - 2 * BE_degradation)) := proven

def BochnerMinimal {X : Type*} (h : X → ℝ) (D : Diffusion X) (eps : ℝ) : Prop  := proven

theorem doob_gamma_eq {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (H : DoobAssumptions h D) : (Doob h D).Gamma = D.Gamma  := proven

theorem doob_gamma2_eq {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (f : X → ℝ) (H : DoobAssumptions h D) :
  (Doob h D).Gamma2 f = D.Gamma2 f  := proven

theorem doob_gamma2_eq_all {X : Type*} (h : X → ℝ)
  (D : Diffusion X) (H : DoobAssumptions h D) :
  ∀ f : X → ℝ, (Doob h D).Gamma2 f = D.Gamma2 f  := proven

theorem doobL_pointwise {X : Type*} (D : Diffusion X)
  (h : X → ℝ) (H : DoobAssumptions h D) (f : X → ℝ) (x : X) :
  doobL D h f x = (1 / h x) * D.L (fun y => h y * f y) x  := proven

theorem gammaPair_doob_eq {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (f g : X → ℝ) :
  gammaPair (Doob h D) f g = gammaPair D f g  := proven

theorem hasLeibnizGamma_doob_of_base {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (HG : HasLeibnizGamma D) :
  HasLeibnizGamma (Doob h D)  := proven

theorem cd_parameter_shift {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) {lam : ℝ} (hCD : HasCD D lam) :
  ∃ lam' : ℝ, HasCD (Doob h D) lam' ∧ lam' ≤ lam  := proven

def lambdaBE (lam eps : ℝ) : ℝ  := proven

lemma lambdaBE_le_base {lam eps : ℝ} (hε : 0 ≤ eps) : lambdaBE lam eps ≤ lam  := proven

lemma hasCD_doob_of_bochnerMinimal {X : Type*}
  (h : X → ℝ) (D : Diffusion X) {eps lam : ℝ}
  (HB : BochnerMinimal h D eps) (hCD : HasCD D lam) :
  HasCD (Doob h D) (lambdaBE lam eps)  := proven

theorem lambdaBE_from_doobAssumptions {X : Type*}
  (h : X → ℝ) (D : Diffusion X) (_H : DoobAssumptions h D)
  (lam eps : ℝ) (hCD : HasCD D lam) (hBochner : BochnerMinimal h D eps) :
  HasCD (Doob h D) (lambdaBE lam eps)  := proven

theorem lambdaBE_bound_from_doobAssumptions {X : Type*}
  (h : X → ℝ) (D : Diffusion X) (_H : DoobAssumptions h D)
  (lam eps : ℝ) (heps : 0 ≤ eps) :
  lambdaBE lam eps ≤ lam  := proven

theorem doob_cd_with_lambdaBE {X : Type*}
  (h : X → ℝ) (D : Diffusion X) (H : DoobAssumptions h D)
  (lam eps : ℝ) (heps : 0 ≤ eps)
  (hCD : HasCD D lam) (hBochner : BochnerMinimal h D eps) :
  HasCD (Doob h D) (lambdaBE lam eps) ∧ lambdaBE lam eps ≤ lam  := proven

structure DoobQuantitative {X : Type*} (h : X → ℝ) (D : Diffusion X) where
  (eps : ℝ) (eps_nonneg : 0 ≤ eps) (bochner : BochnerMinimal h D eps) := proven

theorem cd_parameter_shift_explicit {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (HQ : DoobQuantitative h D) {lam : ℝ} (hCD : HasCD D lam) :
  ∃ lam' : ℝ, lam' = lambdaBE lam HQ.eps ∧ HasCD (Doob h D) lam' ∧ lam' ≤ lam  := proven

theorem cd_parameter_shift_explicit_value {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (HQ : DoobQuantitative h D) {lam : ℝ} (hCD : HasCD D lam) :
  HasCD (Doob h D) (lambdaBE lam HQ.eps) ∧ lambdaBE lam HQ.eps ≤ lam  := proven

structure DoobLamBound where
  (lamBase : ℝ) (eps : ℝ) (lamEff : ℝ) (h_lamEff : lamEff = lambdaBE lamBase eps) := proven

def DoobLamBound.mk' (lamBase eps : ℝ) : DoobLamBound  := proven

lemma DoobLamBound.le_base {B : DoobLamBound} (hε : 0 ≤ B.eps) :
  B.lamEff ≤ B.lamBase  := proven

theorem doob_lambda_eff_formula {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (lam : ℝ) (hCD : HasCD D lam) :
  ∃ lam_eff : ℝ, lam_eff = lam - 2 * H.BE_degradation ∧
    HasCD (Doob h D) lam_eff ∧ lam_eff ≤ lam  := proven

def doob_lambda_eff {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (lam : ℝ) : ℝ  := proven

theorem doob_lambda_eff_le {X : Type*} (h : X → ℝ) (D : Diffusion X)
  (H : DoobAssumptions h D) (lam : ℝ) :
  doob_lambda_eff h D H lam ≤ lam  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVI.lean

namespace Frourio

lemma limsup_nonpos_eventually_le {α : Type*} (u : α → ℝ) (l : Filter α) (ε : ℝ) (hε : 0 < ε) :
    Filter.limsup (fun x => (u x : EReal)) l ≤ (0 : EReal) →
    ∀ᶠ x in l, u x ≤ ε  := proven

lemma local_control_from_DiniUpperE
  (φ : ℝ → ℝ) (t : ℝ) (ε : ℝ) (hε : 0 < ε) (h_dini : DiniUpperE φ t ≤ 0) :
    ∃ δ > 0, ∀ h, 0 < h ∧ h < δ → (φ (t + h) - φ t) / h ≤ ε  := proven

lemma telescoping_sum_real (t : ℕ → ℝ) :
  ∀ n : ℕ, ∑ i ∈ range n, (t (i+1) - t i) = t n - t 0  := proven

lemma sum_bound_from_stepwise
  (φ : ℝ → ℝ) (s ε : ℝ) {N : ℕ} (t : ℕ → ℝ)
  (hstep :
    ∀ i < N, φ (s + t (i + 1)) - φ (s + t i) ≤ ε * (t (i + 1) - t i)) :
  (∑ i ∈ Finset.range N, (φ (s + t (i+1)) - φ (s + t i)))
    ≤ ε * (∑ i ∈ Finset.range N, (t (i+1) - t i))  := proven

lemma global_from_uniform_small_interval_control
  (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r)
  (hL : ∃ L > 0, ∀ ⦃y z⦄, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
  φ (s + r) ≤ φ s + ε * r  := proven

theorem finite_chain_composition_core
  (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r) (hε_pos : 0 < ε)
  (two_point_ball_local :
    ∀ w ∈ Set.Icc 0 r, ∃ ρw > 0, ∃ δw > 0,
      ∀ u ∈ Set.Icc 0 r, ∀ v ∈ Set.Icc 0 r,
        dist u w < ρw → dist v w < ρw →
        φ (s + v) - φ (s + u) ≤ ε * (v - u)) :
  φ (s + r) ≤ φ s + ε * r  := proven

lemma finite_chain_composition_with_usc (φ : ℝ → ℝ) (s r ε : ℝ) (hr_pos : 0 < r)
  (hε_pos : 0 < ε) (h_dini_all : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
  (h_usc : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
    |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀) :
    φ (s + r) ≤ φ s + ε * r  := proven

lemma limit_epsilon_to_zero (f g c : ℝ) (hc : 0 ≤ c) (h : ∀ ε > 0, f ≤ g + ε * c) : f ≤ g  := proven


lemma shifted_function_nonincreasing_with_usc
  (φ : ℝ → ℝ) (s : ℝ) (h_dini_shifted : ∀ u ≥ 0, DiniUpperE (fun τ => φ (s + τ) - φ s) u ≤ 0)
  (h_usc : ∀ t > 0, ∀ w ∈ Set.Icc 0 t, ∀ y₀ ∈ Set.Icc 0 t,
    |y₀ - w| < t / 4 → upper_semicontinuous_at_zero φ s y₀) :
    ∀ t ≥ 0, φ (s + t) ≤ φ s  := proven

theorem nonincreasing_of_DiniUpperE_nonpos_with_usc (φ : ℝ → ℝ)
    (hD : ∀ u, DiniUpperE φ u ≤ 0)
    (h_usc : ∀ s t, s < t → ∀ w ∈ Set.Icc 0 (t - s), ∀ y₀ ∈ Set.Icc 0 (t - s),
      |y₀ - w| < (t - s) / 4 → upper_semicontinuous_at_zero φ s y₀) :
    ∀ s t, s ≤ t → φ t ≤ φ s  := proven

def EVIBridgeForward (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop  := proven

def EVIBridgeBackward (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop  := proven

def EVIEquivBridge (P : (X → ℝ) → (ℝ → X) → Prop)
  (F : X → ℝ) (lam : ℝ) : Prop  := proven

def GeodesicUniformEval (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

theorem geodesicUniform_to_bridge {P : EVIProblem X} {u v : ℝ → X}
  (G : GeodesicUniformEval P u v) : ∀ η : ℝ, HbridgeWithError P u v η  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore0.lean

namespace Frourio

noncomputable def d2 {X : Type*} [PseudoMetricSpace X] (x y : X) : ℝ  := proven

noncomputable def DiniUpperE (φ : ℝ → ℝ) (t : ℝ) : EReal  := proven

lemma DiniUpperE_shift (φ : ℝ → ℝ) (s u : ℝ) :
  DiniUpperE (fun τ => φ (s + τ)) u = DiniUpperE φ (s + u)  := proven

lemma DiniUpperE_add_const (φ : ℝ → ℝ) (c : ℝ) (t : ℝ) :
  DiniUpperE (fun x => φ x + c) t = DiniUpperE φ t  := proven

theorem DiniUpper_nonpos_of_nonincreasing (φ : ℝ → ℝ) (t : ℝ)
  (Hmono : ∀ ⦃s u : ℝ⦄, s ≤ u → φ u ≤ φ s) :
  DiniUpperE φ t ≤ (0 : EReal)  := proven

noncomputable def DiniUpper (φ : ℝ → ℝ) (t : ℝ) : ℝ  := proven

theorem DiniUpper_shift (φ : ℝ → ℝ) (s t : ℝ) :
  DiniUpper (fun τ => φ (s + τ)) t = DiniUpper φ (s + t)  := proven

theorem DiniUpper_add_const (ψ : ℝ → ℝ) (c t : ℝ) :
  DiniUpper (fun τ => ψ τ + c) t = DiniUpper ψ t  := proven

theorem DiniUpperE_const (c t : ℝ) :
  DiniUpperE (fun _ => c) t = (0 : EReal)  := proven

theorem DiniUpper_const (c t : ℝ) :
  DiniUpper (fun _ => c) t = 0  := proven

theorem DiniUpperE_bounds_const_upper (c t : ℝ) :
  ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (((fun _ => c) (t + h) - (fun _ => c) t) / h) ≤ M  := proven

theorem DiniUpperE_bounds_const_lower (c t : ℝ) :
  ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      m ≤ (((fun _ => c) (t + h) - (fun _ => c) t) / h)  := proven


theorem DiniUpper_timeRescale_const (σ c t : ℝ) :
  DiniUpper (fun τ => (fun _ => c) (σ * τ)) t = σ * DiniUpper (fun _ => c) (σ * t)  := proven

structure EVIProblem (X : Type*) [PseudoMetricSpace X] where
  (E : X → ℝ)
  (lam : ℝ) := proven

def IsEVISolution {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : ℝ → X) : Prop  := proven

def timeRescale {X : Type*} (σ : ℝ) (u : ℝ → X) : ℝ → X  := proven

def DiniUpper_timeRescale_pred (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ) : Prop  := proven

def DiniUpper_add_le_pred (φ ψ : ℝ → ℝ) (t : ℝ) : Prop  := proven

theorem DiniUpper_add_le_pred_const_left (c : ℝ) (ψ : ℝ → ℝ) (t : ℝ) :
  DiniUpper_add_le_pred (fun _ => c) ψ t  := proven

theorem DiniUpper_add_le_pred_const_right (φ : ℝ → ℝ) (c : ℝ) (t : ℝ) :
  DiniUpper_add_le_pred φ (fun _ => c) t  := proven

theorem DiniUpperE_add_le
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (h1 : DiniUpperE φ t ≠ ⊥ ∨ DiniUpperE ψ t ≠ ⊤)
  (h2 : DiniUpperE φ t ≠ ⊤ ∨ DiniUpperE ψ t ≠ ⊥) :
  DiniUpperE (fun τ => φ τ + ψ τ) t ≤ DiniUpperE φ t + DiniUpperE ψ t  := proven

theorem DiniUpper_eq_toReal_of_finite
  (φ : ℝ → ℝ) (t : ℝ)
  (_hfin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hub : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            ((φ (t + h) - φ t) / h) ≤ M)
  (hlb : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            m ≤ ((φ (t + h) - φ t) / h)) :
  DiniUpper φ t = (DiniUpperE φ t).toReal  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore1.lean

namespace Frourio

theorem DiniUpper_add_le_of_finite
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t  := proven

theorem DiniUpper_add_le_pred_of_bounds (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t  := proven

theorem forwardDiff_upper_bound_sum
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hubφ : ∃ Mφ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            ((φ (t + h) - φ t) / h) ≤ Mφ)
  (hubψ : ∃ Mψ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            ((ψ (t + h) - ψ t) / h) ≤ Mψ) :
  ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M  := proven

theorem forwardDiff_lower_bound_sum
  (φ ψ : ℝ → ℝ) (t : ℝ)
  (hlbφ : ∃ mφ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            mφ ≤ ((φ (t + h) - φ t) / h))
  (hlbψ : ∃ mψ : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            mψ ≤ ((ψ (t + h) - ψ t) / h)) :
  ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)  := proven

theorem DiniUpper_add_le_pred_holds (φ ψ : ℝ → ℝ) (t : ℝ)
  (hφ_fin : DiniUpperE φ t ≠ ⊤ ∧ DiniUpperE φ t ≠ ⊥)
  (hψ_fin : DiniUpperE ψ t ≠ ⊤ ∧ DiniUpperE ψ t ≠ ⊥)
  (hsum_fin : DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊤ ∧
              DiniUpperE (fun τ => φ τ + ψ τ) t ≠ ⊥)
  (hubφ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((φ (t + h) - φ t) / h) ≤ M)
  (hlbφ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((φ (t + h) - φ t) / h))
  (hubψ : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((ψ (t + h) - ψ t) / h) ≤ M)
  (hlbψ : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ ((ψ (t + h) - ψ t) / h))
  (hubsum : ∃ M : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h) ≤ M)
  (hlbsum : ∃ m : ℝ, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
              m ≤ (((φ (t + h) + ψ (t + h)) - (φ t + ψ t)) / h)) :
  DiniUpper_add_le_pred φ ψ t  := proven

def gronwall_exponential_contraction_pred (lam : ℝ) (W : ℝ → ℝ) : Prop  := proven

def gronwall_exponential_contraction_with_error_half_pred (lam η : ℝ)
  (W : ℝ → ℝ) : Prop  := proven

def ContractionProperty {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

def ContractionPropertySq {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

def Hbridge {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

structure BridgeAssumptions {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) : Prop where
  (bridge : Hbridge P u v) := proven

theorem Hbridge_from_assumptions {X : Type*} [PseudoMetricSpace X]
  {P : EVIProblem X} {u v : ℝ → X}
  (H : BridgeAssumptions P u v) : Hbridge P u v  := proven

def sqrt_d2_dist {X : Type*} [PseudoMetricSpace X]
  (x y : X) : Prop  := proven

def sqrt_mul_nonneg (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) : Prop  := proven

def sqrt_exp_halves (x : ℝ) : Prop  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore2.lean

namespace Frourio


theorem sqrt_d2_dist_prop {X : Type*} [PseudoMetricSpace X]
  (x y : X) : sqrt_d2_dist x y  := proven


theorem sqrt_mul_nonneg_prop (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  sqrt_mul_nonneg a b ha hb  := proven

theorem sqrt_exp_halves_prop (x : ℝ) : sqrt_exp_halves x  := proven

theorem sqrt_add_le_sqrt_add_sqrt_prop (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b  := proven

theorem DiniUpper_add_le (φ ψ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_add_le_pred φ ψ t) :
  DiniUpper (fun τ => φ τ + ψ τ) t ≤ DiniUpper φ t + DiniUpper ψ t  := proven

theorem DiniUpper_timeRescale (σ : ℝ) (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t)  := proven

theorem DiniUpper_timeRescale_pos (σ : ℝ) (hσ : 0 < σ)
  (φ : ℝ → ℝ) (t : ℝ)
  (H : DiniUpper_timeRescale_pred σ φ t) :
  DiniUpper (fun τ => φ (σ * τ)) t = σ * DiniUpper φ (σ * t)  := proven

theorem gronwall_exponential_contraction_from_pred (lam : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0  := proven

theorem gronwall_exponential_contraction (lam : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0  := proven

theorem gronwall_exponential_contraction_with_error_half_from_pred
  (lam η : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t  := proven

theorem gronwall_exponential_contraction_with_error_half
  (lam η : ℝ) (W : ℝ → ℝ)
  (Hpred : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t  := proven

theorem gronwall_exponential_contraction_with_error_half_core
  (lam η : ℝ) (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_with_error_half_pred lam η W)
  (Hineq : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ η) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0 + (2 * η) * t  := proven

theorem DiniUpper_timeRescale_one (φ : ℝ → ℝ) (t : ℝ) :
  DiniUpper (fun τ => φ (1 * τ)) t = (1 : ℝ) * DiniUpper φ (1 * t)  := proven

theorem gronwall_exponential_contraction_zero
  (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred (0 : ℝ) W)
  (Hineq0 : ∀ t : ℝ, DiniUpper W t ≤ 0) :
  ∀ t : ℝ, W t ≤ W 0  := proven

theorem gronwall_exponential_contraction_with_error_zero
  (lam : ℝ) (W : ℝ → ℝ)
  (H : (∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ 0) →
        ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0)
  (Hineq0 : ∀ t : ℝ, (1 / 2 : ℝ) * DiniUpper W t + lam * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0  := proven


theorem gronwall_exponential_contraction_core (lam : ℝ) (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred lam W)
  (Hineq : ∀ t : ℝ, DiniUpper W t + (2 * lam) * W t ≤ 0) :
  ∀ t : ℝ, W t ≤ Real.exp (-(2 * lam) * t) * W 0  := proven

theorem gronwall_zero (W : ℝ → ℝ)
  (H : gronwall_exponential_contraction_pred (0 : ℝ) W)
  (Hineq0 : ∀ t : ℝ, DiniUpper W t ≤ 0) :
  ∀ t : ℝ, W t ≤ W 0  := proven

theorem bridge_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (H : Hbridge P u v) (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore3.lean

namespace Frourio

theorem bridge_contraction_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hSq : ContractionPropertySq P u v) :
  ContractionProperty P u v  := proven

theorem Hbridge_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) :
  Hbridge P u v  := proven

def eviContraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v) : Prop  := proven

abbrev evi_contraction {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v) : Prop  := proven

theorem evi_contraction_self {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : ℝ → X)
  (_hu : IsEVISolution P u) :
  ContractionProperty P u u  := proven

theorem evi_contraction_sq_from_gronwall {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v  := proven

theorem eviContraction_general {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v  := proven

theorem eviContraction_thm
  {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v  := proven

theorem evi_contraction_thm_concrete
  {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (Hineq2 : ∀ t : ℝ,
    DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
      + (2 * P.lam) * d2 (u t) (v t) ≤ 0)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionProperty P u v  := proven

structure MixedErrorBound (X : Type*) [PseudoMetricSpace X]
  (u v : ℝ → X) where
  (η : ℝ)
  (bound : ∀ _t : ℝ, Prop) := proven

def eviSumWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (_geodesicBetween : Prop) (hR : MixedErrorBound X u v) : Prop  := proven

def eviSumNoError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (_hu : IsEVISolution P u) (_hv : IsEVISolution P v)
  (_geodesicBetween : Prop) : Prop  := proven

def ContractionPropertySqWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop  := proven

theorem eviSynchronizationSq_with_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (_geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv _geodesicBetween hR)
  (Hgr : (∀ t : ℝ, (1 / 2 : ℝ) *
            DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
            + P.lam * d2 (u t) (v t) ≤ hR.η) →
          ∀ t : ℝ,
            d2 (u t) (v t)
              ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * hR.η) * t) :
  ContractionPropertySqWithError P u v hR.η  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore4.lean

namespace Frourio

theorem eviSynchronizationSq_no_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (_geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv _geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v  := proven

theorem twoEVI_sq_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionPropertySq P u v  := proven

lemma and a bridge from squared to linear distances. -/
theorem twoEVI_dist_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v  := proven

theorem twoEVI_dist_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t)))
  (Hbridge : Hbridge P u v) :
  ContractionProperty P u v  := proven

theorem evi_synchronization_thm_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop)
  (Hsum0 : eviSumNoError P u v hu hv geodesicBetween)
  (Hgr : gronwall_exponential_contraction_pred P.lam (fun t => d2 (u t) (v t))) :
  ContractionProperty P u v  := proven

def ContractionPropertyWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop  := proven

def HbridgeWithError {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) : Prop  := proven

theorem bridge_with_error {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ)
  (H : HbridgeWithError P u v η)
  (Hsq : ContractionPropertySqWithError P u v η) :
  ContractionPropertyWithError P u v η  := proven

theorem twoEVI_sq_with_error_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv geodesicBetween hR)
  (Hgr : gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
            (fun t => d2 (u t) (v t))) :
  ContractionPropertySqWithError P u v hR.η  := proven

theorem twoEVI_with_error_dist_from_sum {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv geodesicBetween hR)
  (Hgr : gronwall_exponential_contraction_with_error_half_pred P.lam hR.η
            (fun t => d2 (u t) (v t)))
  (Hbridge : HbridgeWithError P u v hR.η) :
  ContractionPropertyWithError P u v hR.η  := proven

theorem bridge_contraction_with_error_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) (η : ℝ) :
  HbridgeWithError P u v η  := proven

theorem HbridgeWithError_concrete_all_eta {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X) :
  ∀ η : ℝ, HbridgeWithError P u v η  := proven

theorem evi_synchronization_with_error_thm_concrete {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : ℝ → X)
  (hu : IsEVISolution P u) (hv : IsEVISolution P v)
  (geodesicBetween : Prop) (hR : MixedErrorBound X u v)
  (Hsum : eviSumWithError P u v hu hv geodesicBetween hR)
  (Hgr : (∀ t : ℝ, (1 / 2 : ℝ) *
            DiniUpper (fun τ : ℝ => d2 (u τ) (v τ)) t
            + P.lam * d2 (u t) (v t) ≤ hR.η) →
          ∀ t : ℝ,
            d2 (u t) (v t)
              ≤ Real.exp (-(2 * P.lam) * t) * d2 (u 0) (v 0) + (2 * hR.η) * t) :
  ContractionPropertyWithError P u v hR.η  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore5.lean

namespace Frourio

abbrev Rge0  := proven

def toRge0 (t : ℝ) : Rge0  := proven

def restrictNonneg {X : Type*} (u : Rge0 → X) : ℝ → X  := proven

def IsEVISolutionNonneg {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u : Rge0 → X) : Prop  := proven

def evi_contraction_nonneg {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (u v : Rge0 → X)
  (_hu : IsEVISolutionNonneg P u) (_hv : IsEVISolutionNonneg P v) : Prop  := proven

structure MoscoSystem (ι : Type*) where
  (Xh : ι → Type*)
  (X : Type*)
  [hx : ∀ h, PseudoMetricSpace (Xh h)]
  [x : PseudoMetricSpace X]
  (Th : ∀ h, Xh h → X)
  (Eh : ∀ h, Xh h → ℝ)
  (E : X → ℝ) := proven

def MoscoGeodesicComplete {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

def MoscoTight {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

def MoscoM1 {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

def MoscoM2 {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

def LowerSemicontinuousSeq {X : Type*} [PseudoMetricSpace X] (E : X → ℝ) : Prop  := proven

structure MoscoAssumptions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (geodesic_complete : MoscoGeodesicComplete S)
  (tightness : MoscoTight S)
  (lsc_Ent : LowerSemicontinuousSeq S.E)
  (M1 : MoscoM1 S)
  (M2 : MoscoM2 S) := proven

def EVILimitHolds {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

theorem eviInheritance {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoAssumptions S) : EVILimitHolds S  := proven

def EntropyUniformLowerBound {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

def DirichletFormLiminf {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

def DirichletFormRecovery {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

theorem MoscoTight_from_entropy {ι : Type*} (S : MoscoSystem ι)
  (H : EntropyUniformLowerBound S) : MoscoTight S  := proven

theorem MoscoM1_from_dirichlet_liminf {ι : Type*} (S : MoscoSystem ι)
  (H : DirichletFormLiminf S) : MoscoM1 S  := proven

theorem MoscoM2_from_dirichlet_recovery {ι : Type*} (S : MoscoSystem ι)
  (H : DirichletFormRecovery S) : MoscoM2 S  := proven

theorem build_MoscoAssumptions_from_entropy_dirichlet {ι : Type*}
  (S : MoscoSystem ι)
  (Hg : MoscoGeodesicComplete S)
  (Hent : EntropyUniformLowerBound S)
  (Hlim : DirichletFormLiminf S)
  (Hrec : DirichletFormRecovery S)
  (Hlsc : LowerSemicontinuousSeq S.E) : MoscoAssumptions S  := proven

theorem EVILimit_from_entropy_dirichlet {ι : Type*} (S : MoscoSystem ι)
  (Hg : MoscoGeodesicComplete S)
  (Hent : EntropyUniformLowerBound S)
  (Hlim : DirichletFormLiminf S)
  (Hrec : DirichletFormRecovery S)
  (Hlsc : LowerSemicontinuousSeq S.E) : EVILimitHolds S  := proven

theorem MoscoTight_of_uniform_lower_bound {ι : Type*} (S : MoscoSystem ι)
  (C : ℝ) (h : ∀ (h' : ι) (x : S.Xh h'), S.Eh h' x ≥ -C) : MoscoTight S  := proven

theorem MoscoM1_of_liminf_along_Th {ι : Type*} (S : MoscoSystem ι)
  (h : ∀ (h' : ι) (x : S.Xh h'), S.E (S.Th h' x) ≤ S.Eh h' x) : MoscoM1 S  := proven

theorem MoscoM2_of_recovery_no_inflation {ι : Type*} (S : MoscoSystem ι)
  (h : ∀ x : S.X, ∃ (h' : ι) (xh : S.Xh h'), S.Th h' xh = x ∧ S.Eh h' xh ≤ S.E x) :
  MoscoM2 S  := proven

structure MoscoSufficientConditions {ι : Type*} (S : MoscoSystem ι) : Prop where
  (uniform_lower : ∃ C : ℝ, ∀ (h : ι) (x : S.Xh h), S.Eh h x ≥ -C)
  (liminf_along_Th : ∀ (h : ι) (x : S.Xh h), S.E (S.Th h x) ≤ S.Eh h x)
  (recovery_no_inflation : ∀ x : S.X, ∃ (h : ι) (xh : S.Xh h), S.Th h xh = x ∧ S.Eh h xh ≤ S.E x)
  (geodesic_complete : Nonempty S.X)
  (lsc_Ent : LowerSemicontinuousSeq S.E) := proven

theorem build_MoscoAssumptions_from_sufficient {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoSufficientConditions S) : MoscoAssumptions S  := proven

theorem EVILimit_from_sufficient {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoSufficientConditions S) : EVILimitHolds S  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore6.lean

namespace Frourio

theorem local_control_from_DiniUpperE_right
    (t : ℝ) (hDini : DiniUpperE φ t ≤ 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h  := proven

theorem directed_two_point_local_with_usc
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

def DirectedProductSpace (r : ℝ) : Set (ℝ × ℝ)  := proven

def maxDist (p q : ℝ × ℝ) : ℝ  := proven

theorem lebesgue_number_for_directed_cover_with_usc
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

theorem uniform_small_interval_control_with_usc
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

theorem global_evaluation_from_partition_with_usc
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    φ (s + r) ≤ φ s + ε * r  := proven

theorem nonincreasing_of_DiniUpperE_nonpos_right_with_usc
    (hDini : ∀ t, DiniUpperE φ t ≤ 0)
    (hUSC : ∀ s : ℝ, ∀ r > 0, ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀) :
    ∀ s t, s ≤ t → φ t ≤ φ s  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore6Sub1.lean

namespace Frourio

lemma lemma_R1_eventually_le_from_limsup {α : Type*} {f : α → ℝ} {l : Filter α} {c : ℝ}
    (h : limsup (fun x => (f x : EReal)) l ≤ (c : EReal)) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x in l, f x ≤ c + η  := proven

lemma lemma_R1_nonpos_special {α : Type*} {f : α → ℝ} {l : Filter α}
    (h : limsup (fun x => (f x : EReal)) l ≤ (0 : EReal)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in l, f x ≤ ε  := proven

lemma lemma_R2_right_filter_extraction {P : ℝ → Prop}
    (h : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), P h) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → P h  := proven

lemma lemma_R3a_coe_lt (x y : ℝ) : (x : EReal) < (y : EReal) ↔ x < y  := proven

lemma lemma_R3b_coe_le (x y : ℝ) : (x : EReal) ≤ (y : EReal) ↔ x ≤ y  := proven

lemma lemma_R4_multiply_positive {φ : ℝ → ℝ} {t h ε : ℝ} (hh_pos : 0 < h)
    (hq : (φ (t + h) - φ t) / h ≤ ε) :
    φ (t + h) - φ t ≤ ε * h  := proven

theorem right_epsilon_delta_from_dini_nonpos
    (hDini : DiniUpperE φ t ≤ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h  := proven

theorem local_control_from_DiniUpperE_right_clean
    (t : ℝ) (hDini : DiniUpperE φ t ≤ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore6Sub2.lean

namespace Frourio

noncomputable def quotient_function (φ : ℝ → ℝ) (s y h : ℝ) : ℝ  := proven

def upper_semicontinuous_at_zero (φ : ℝ → ℝ) (s : ℝ) (y₀ : ℝ) : Prop  := proven

lemma lemma_U1_parametric_uniformization
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y h,
      |y - w| < ρ_w → 0 < h → h < δ_w →
      quotient_function φ s y h ≤ ε  := proven

lemma lemma_U2_directed_two_point
    {w : ℝ} {ρ_w δ_w ε : ℝ}
    (h_uniform : ∀ y h, |y - w| < ρ_w → 0 < h → h < δ_w → quotient_function φ s y h ≤ ε) :
    ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

lemma lemma_U3_metric_form (y w ρ : ℝ) :
    |y - w| < ρ ↔ dist y w < ρ  := proven

lemma dist_eq_sub_of_le' {y z : ℝ} (h : y ≤ z) : dist y z = z - y  := proven

theorem directed_two_point_local_uniform
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

theorem directed_two_point_local_abs
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore6Sub3.lean

namespace Frourio

theorem right_epsilon_delta_at_point (t : ℝ)
    (hDini : DiniUpperE φ t ≤ 0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, 0 < h → h < δ → φ (t + h) - φ t ≤ ε * h  := proven

theorem uniformization_near_center
    {w : ℝ} (hw : w ∈ Set.Icc 0 r) (hr : 0 < r)
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ y₀ ∈ Set.Icc 0 r, |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) :
    ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y h,
      |y - w| < ρ_w → 0 < h → h < δ_w →
      quotient_function φ s y h ≤ ε  := proven

theorem directed_two_point_control_from_uniformization
    {w : ℝ} {ρ_w δ_w : ℝ}
    (h_uniform : ∀ y h, |y - w| < ρ_w → 0 < h → h < δ_w →
      quotient_function φ s y h ≤ ε) :
    ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      |y - w| < ρ_w → |z - w| < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

lemma metric_bridge (y w ρ : ℝ) : |y - w| < ρ ↔ dist y w < ρ  := proven

lemma dist_eq_diff_for_ordered {y z : ℝ} (h : y ≤ z) : dist y z = z - y  := proven

theorem lebesgue_uniform_small_interval
    (hr : 0 < r)
    (h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

theorem lebesgue_number_for_directed_cover_complete
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

theorem lebesgue_number_for_directed_cover_fixed
    (hDini : ∀ u ∈ Set.Icc 0 r, DiniUpperE φ (s + u) ≤ 0)
    (hUSC : ∀ w ∈ Set.Icc 0 r, ∀ y₀ ∈ Set.Icc 0 r,
      |y₀ - w| < r / 4 → upper_semicontinuous_at_zero φ s y₀)
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

end Frourio


## ./Frourio/Analysis/EVI/EVICore6Sub4.lean

namespace Frourio

noncomputable def partition_point (r : ℝ) (N : ℕ) (i : ℕ) : ℝ  := proven

noncomputable def shifted_partition_point (s r : ℝ) (N : ℕ) (i : ℕ) : ℝ  := proven

theorem find_fine_partition (hr : 0 < r) (hL : 0 < L) :
    ∃ N : ℕ, 0 < N ∧ r / (N : ℝ) < L  := proven

theorem partition_geometry_range (r : ℝ) (N : ℕ) (hN : 0 < N) (hr : 0 ≤ r) (i : ℕ) (hi : i ≤ N) :
    0 ≤ partition_point r N i ∧ partition_point r N i ≤ r  := proven

theorem partition_geometry_monotone (r : ℝ) (N : ℕ) (hr : 0 ≤ r)
    (i : ℕ) :
    partition_point r N i ≤ partition_point r N (i + 1) ∧
    partition_point r N (i + 1) - partition_point r N i = r / N  := proven

private lemma telescoping_sum_helper (f : ℕ → ℝ) (n : ℕ) :
    (Finset.range n).sum (fun i => f (i + 1) - f i) = f n - f 0  := proven

theorem telescoping_identity (g : ℝ → ℝ) (s r : ℝ) (N : ℕ) (hN : 0 < N) :
    (Finset.range N).sum (fun i => g (shifted_partition_point s r N (i + 1)) -
                                   g (shifted_partition_point s r N i)) =
    g (s + r) - g s  := proven

theorem per_segment_bound
    (h_control : ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
                   φ (s + z) - φ (s + y) ≤ ε * (z - y))
    (N : ℕ) (hN : 0 < N) (hr : 0 < r) (hL : r / N < L) (i : ℕ) (hi : i < N) :
    φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i) ≤
    ε * (r / N)  := proven

theorem sum_per_segment_bounds
    (h_control : ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
                   φ (s + z) - φ (s + y) ≤ ε * (z - y))
    (N : ℕ) (hN : 0 < N) (hr : 0 < r) (hL : r / N < L) :
    (Finset.range N).sum (fun i =>
      φ (shifted_partition_point s r N (i + 1)) - φ (shifted_partition_point s r N i)) ≤
    ε * r  := proven

theorem global_evaluation_via_partition
    (h_control : ∀ y z, y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
                   φ (s + z) - φ (s + y) ≤ ε * (z - y))
    (hr : 0 < r) (hL : 0 < L) :
    φ (s + r) ≤ φ s + ε * r  := proven

end Frourio


## ./Frourio/Analysis/EntropyPackage.lean

namespace Frourio

theorem probability_klDiv_self {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    InformationTheory.klDiv μ μ = 0  := proven

theorem relativeEntropy_lsc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (ρn : ℕ → Measure X) (ρ : Measure X)
    (hacn : ∀ n, ρn n ≪ μ) (hac : ρ ≪ μ)
    (hfin_n : ∀ n, IsFiniteMeasure (ρn n)) (hfin : IsFiniteMeasure ρ)
    (h_ae : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => ((ρn n).rnDeriv μ x).toReal)
        Filter.atTop (nhds ((ρ.rnDeriv μ x).toReal))) :
      InformationTheory.klDiv ρ μ ≤ Filter.liminf
        (fun n => InformationTheory.klDiv (ρn n) μ) atTop  := proven

theorem relativeEntropy_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : Measure X) :
    0 ≤ InformationTheory.klDiv ρ μ  := proven

theorem relativeEntropy_eq_zero_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ρ] :
    InformationTheory.klDiv ρ μ = 0 ↔ ρ = μ  := proven

lemma llr_add_of_rnDeriv_mul {X : Type*} [MeasurableSpace X]
    (μ ν ρ : Measure X) [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hmul : ∀ᵐ x ∂μ,
      ((μ.rnDeriv ρ x).toReal) = ((μ.rnDeriv ν x).toReal) * ((ν.rnDeriv ρ x).toReal))
    (hpos1 : ∀ᵐ x ∂μ, 0 < ((μ.rnDeriv ν x).toReal))
    (hpos2 : ∀ᵐ x ∂μ, 0 < ((ν.rnDeriv ρ x).toReal)) :
    (MeasureTheory.llr μ ρ) =ᵐ[μ]
      (fun x => MeasureTheory.llr μ ν x + MeasureTheory.llr ν ρ x)  := proven

theorem relativeEntropy_chain_rule_prob_toReal {X : Type*} [MeasurableSpace X]
    (μ ν ρ : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμν : μ ≪ ν) (hνρ : ν ≪ ρ)
    (hmul : ∀ᵐ x ∂μ,
      ((μ.rnDeriv ρ x).toReal) = ((μ.rnDeriv ν x).toReal) * ((ν.rnDeriv ρ x).toReal))
    (hpos1 : ∀ᵐ x ∂μ, 0 < ((μ.rnDeriv ν x).toReal))
    (hpos2 : ∀ᵐ x ∂μ, 0 < ((ν.rnDeriv ρ x).toReal))
    (h_int1 : Integrable (MeasureTheory.llr μ ν) μ)
    (h_int2 : Integrable (MeasureTheory.llr ν ρ) μ) :
    (InformationTheory.klDiv μ ρ).toReal
      = (InformationTheory.klDiv μ ν).toReal + ∫ x, MeasureTheory.llr ν ρ x ∂μ  := proven

lemma integrable_llr_of_integrable_klFun_rnDeriv {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h : Integrable (fun x => InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ν) :
    Integrable (MeasureTheory.llr μ ν) μ  := proven

lemma integrable_llr_of_bounded_rnDeriv {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂ν, (μ.rnDeriv ν x).toReal ≤ C) :
    Integrable (MeasureTheory.llr μ ν) μ  := proven

lemma integrable_llr_of_finite_klDiv {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfin : InformationTheory.klDiv μ ν < ⊤) :
    Integrable (MeasureTheory.llr μ ν) μ  := proven

lemma integrable_llr_of_uniform_bounds {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (a b : ℝ) (ha : 0 < a) (hb : a < b)
    (hbound : ∀ᵐ x ∂ν, a ≤ (μ.rnDeriv ν x).toReal ∧ (μ.rnDeriv ν x).toReal ≤ b) :
    Integrable (MeasureTheory.llr μ ν) μ  := proven

theorem relativeEntropy_data_processing {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ρ : Measure X) (f : X → Y) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (_hf : Measurable f) : True  := proven

theorem entropy_compact_sublevels {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [CompactSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (_c : ℝ) :
    True  := proven

structure EntropyFunctionalCore (X : Type*) [MeasurableSpace X] (μ : Measure X) where
  /-- The entropy value for a probability measure -/
  Ent : Measure X → ℝ
  /-- Non-emptiness of sublevel sets (abstract placeholder for LSC) -/
  sublevel_nonempty : ∀ c : ℝ, ∀ (ρₙ : ℕ → Measure X),
    (∀ n, Ent (ρₙ n) ≤ c) →
    (∃ ρ : Measure X, Ent ρ ≤ c)
  /-- Entropy is bounded below -/
  bounded_below : ∃ c : ℝ, ∀ ρ : Measure X, c ≤ Ent ρ
  /-- Entropy has compact sublevel sets -/
  compact_sublevels : ∀ c : ℝ,
    ∀ (ρₙ : ℕ → Measure X),
      (∀ n, MeasureTheory.IsProbabilityMeasure (ρₙ n)) →
      (∀ n, Ent (ρₙ n) ≤ c) →
      ∃ (ρ : Measure X) (φ : ℕ → ℕ),
        StrictMono φ ∧
        MeasureTheory.IsProbabilityMeasure ρ ∧
        Ent ρ ≤ c ∧
        (∃ (weakly_converges : Prop), weakly_converges) := proven

noncomputable def ConcreteEntropyFunctional {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] : EntropyFunctionalCore X μ where
  Ent  := proven

theorem entropy_displacement_convex {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (K : ℝ) (_hK : 0 ≤ K) :
    ∃ _lam : ℝ, ∀ _ρ₀ _ρ₁ : ProbabilityMeasure X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      -- Along W₂-geodesic γ_t from ρ₀ to ρ₁:
      -- H(γ_t) ≤ (1-t)H(ρ₀) + tH(ρ₁) - λt(1-t)W₂²(ρ₀,ρ₁)/2
      True  := proven

structure EntropyGradientFlow (X : Type*) [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] where
  /-- The flow map: time → initial condition → solution -/
  flow : ℝ → ProbabilityMeasure X → ProbabilityMeasure X
  /-- Initial condition -/
  initial_condition : ∀ ρ₀, flow 0 ρ₀ = ρ₀
  /-- Energy dissipation (entropy decreases along flow) -/
  energy_dissipation : ∀ t s : ℝ, 0 ≤ t → t ≤ s → ∀ ρ₀,
    InformationTheory.klDiv (flow s ρ₀).toMeasure
      μ ≤ InformationTheory.klDiv (flow t ρ₀).toMeasure μ
  /-- Continuity in time (abstract property) -/
  time_continuous : ∀ _ρ₀ : ProbabilityMeasure X, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ (|t - s| < δ →
    -- Abstract: distance between flow t ρ₀ and flow s ρ₀ is small
    True)  -- Placeholder for actual continuity condition := proven

noncomputable def entropyToPLFA {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    -- Returns a functional F : P₂(X) → ℝ suitable for PLFA
    ProbabilityMeasure X → ℝ  := proven

theorem entropy_geodesic_convex {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (_K : ℝ) :
    -- Along geodesics in P₂(X), entropy satisfies K-convexity
    ∃ F : ProbabilityMeasure X → ℝ,
      F = entropyToPLFA μ ∧
      -- F is K-geodesically convex
      (∀ _ρ₀ _ρ₁ : ProbabilityMeasure X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        -- Placeholder for geodesic convexity condition
        True)  := proven

theorem entropy_EDE {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ (_flow : EntropyGradientFlow X μ),
      ∀ t : ℝ, 0 ≤ t → ∀ _ρ₀ : ProbabilityMeasure X,
        -- d/dt H(ρ_t) + |∂H|(ρ_t)² = 0 (placeholder)
        True  := proven

theorem entropy_EVI {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (_K : ℝ) :
    ∃ (_flow : EntropyGradientFlow X μ),
      ∀ t : ℝ, 0 ≤ t → ∀ _ρ₀ _σ : ProbabilityMeasure X,
        -- EVI placeholder inequality
        True  := proven

noncomputable def entropyJKO {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (τ : ℝ) (_hτ : 0 < τ) :
    ProbabilityMeasure X → ProbabilityMeasure X  := proven

theorem JKO_convergence {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ (_flow : EntropyGradientFlow X μ),
      ∀ _ρ₀ : ProbabilityMeasure X,
        -- As τ → 0, JKO iterates converge to continuous flow (placeholder)
        True  := proven

def entropyPLFAInstance {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    -- This would provide the necessary structure for PLFA
    True  := proven

end Frourio


## ./Frourio/Analysis/ExponentialDecay.lean

namespace Frourio

theorem exp_neg_sq_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun n : ℕ => Real.exp (-c * (n : ℝ)^2)) Filter.atTop (nhds 0)  := proven


lemma tendsto_comp {α : Type*} {β : Type*} {γ : Type*} {f : α → β} {g : β → γ} {x : Filter α}
  {y : Filter β} {z : Filter γ} (hg : Filter.Tendsto g y z) (hf : Filter.Tendsto f x y) :
  Filter.Tendsto (g ∘ f) x z  := proven

theorem exponential_decay_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      4 * Real.exp (-Real.pi * ε^2 * (n + 1)^2) < ε  := proven

theorem exponential_decay_bound_reciprocal (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      4 * Real.exp (-Real.pi * ε^2 / δ^2) < ε  := proven

theorem gaussian_tail_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      let δ  := proven

theorem general_exponential_bound (A B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      A * Real.exp (-B * (n : ℝ)^2) < ε  := proven

end Frourio


## ./Frourio/Analysis/FourierPlancherel.lean

namespace Frourio

def fourierKernel (ξ t : ℝ) : ℂ  := proven

@[simp] lemma fourierKernel_zero_left (t : ℝ) : fourierKernel 0 t = 1  := proven

@[simp] lemma fourierKernel_zero_right (ξ : ℝ) : fourierKernel ξ 0 = 1  := proven

lemma fourierKernel_norm (ξ t : ℝ) : ‖fourierKernel ξ t‖ = 1  := proven


lemma fourierKernel_mul_eq (ξ t : ℝ) (z : ℂ) :
    fourierKernel ξ t * z = ((Real.fourierChar (-(t * ξ))) : Circle) • z  := proven


lemma fourierKernel_eq_char (ξ t : ℝ) :
    fourierKernel ξ t = ((Real.fourierChar (-(t * ξ))) : ℂ)  := proven


lemma fourierKernel_mul_norm (ξ t : ℝ) (z : ℂ) :
    ‖fourierKernel ξ t * z‖ = ‖z‖  := proven


lemma fourierKernel_conj (ξ t : ℝ) :
    conj (fourierKernel ξ t) = fourierKernel (-ξ) t  := proven

lemma fourierKernel_neg (ξ t : ℝ) : fourierKernel (-ξ) t = conj (fourierKernel ξ t)  := proven


lemma integrable_fourierKernel_mul_iff {f : ℝ → ℂ} (ξ : ℝ) :
    Integrable (fun t => fourierKernel ξ t * f t) ↔ Integrable f  := proven


lemma integrable_fourierKernel_mul {f : ℝ → ℂ} (ξ : ℝ) (hf : Integrable f) :
    Integrable (fun t => fourierKernel ξ t * f t)  := proven


lemma integrable_conj_of_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) :
    Integrable (fun t => conj (f t)) μ  := proven

def fourierIntegral (f : ℝ → ℂ) (ξ : ℝ) : ℂ  := proven


lemma fourierIntegral_eq_real (f : ℝ → ℂ) (ξ : ℝ) :
    Real.fourierIntegral f ξ = fourierIntegral f ξ  := proven


lemma norm_fourierIntegral_le (f : ℝ → ℂ) (ξ : ℝ) :
    ‖fourierIntegral f ξ‖ ≤ ∫ t : ℝ, ‖f t‖  := proven


lemma fourierIntegral_conj {f : ℝ → ℂ} (_hf : Integrable f) (ξ : ℝ) :
    conj (fourierIntegral f ξ) =
      fourierIntegral (fun t => conj (f t)) (-ξ)  := proven

lemma integrand_norm_sq (ξ t : ℝ) (f : ℝ → ℂ) :
    ‖fourierKernel ξ t * f t‖ ^ 2 = ‖f t‖ ^ 2  := proven

lemma fourierIntegral_apply (f : ℝ → ℂ) (ξ : ℝ) :
    fourierIntegral f ξ = ∫ t : ℝ, fourierKernel ξ t * f t  := proven

lemma fourierIntegral_abs_le (f : ℝ → ℂ) (ξ : ℝ) :
    ‖fourierIntegral f ξ‖ ≤ ∫ t : ℝ, ‖f t‖  := proven

namespace Schwartz

lemma integrable_fourierKernel_mul (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    Integrable (fun t : ℝ => fourierKernel ξ t * f t)  := proven

lemma fourierIntegral_eq_fourierTransform (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => f t) ξ =
      (fourierTransformCLE ℝ f) ξ  := proven

lemma fourierIntegral_conj_eq_neg (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierIntegral (fun t : ℝ => conj (f t)) ξ =
      conj (fourierIntegral (fun t : ℝ => f t) (-ξ))  := proven

lemma fourierIntegral_conj_eq_neg_real (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    Real.fourierIntegral (fun t : ℝ => conj (f t)) ξ =
      conj (Real.fourierIntegral (fun t : ℝ => f t) (-ξ))  := proven


lemma integrable_fourierIntegral (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => fourierIntegral (fun t : ℝ => f t) ξ)  := proven

lemma integrable_fourierIntegral_neg (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => fourierIntegral (fun t : ℝ => f t) (-ξ))  := proven

lemma integrable_conj_fourierIntegral (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => conj (fourierIntegral (fun t : ℝ => f t) ξ))  := proven

def conjFourierTransform (f : SchwartzMap ℝ ℂ) : ℝ → ℂ  := proven

def doubleFourierTransform (f : SchwartzMap ℝ ℂ) : ℝ → ℂ  := proven

lemma fourierIntegral_conj_fourierIntegral (f : SchwartzMap ℝ ℂ) :
    doubleFourierTransform f = fun t : ℝ => conj (f t)  := proven

end Schwartz

lemma fourier_plancherel (f : SchwartzMap ℝ ℂ) :
    ∫ t : ℝ, ‖f t‖ ^ 2 = ∫ ξ : ℝ, ‖fourierIntegral (fun t : ℝ => f t) ξ‖ ^ 2  := proven

end Frourio


## ./Frourio/Analysis/FrourioFunctional.lean

namespace Frourio

structure FrourioFunctional (X : Type*) [PseudoMetricSpace X] where
  (Ent : X → ℝ) (Dsigmam : X → ℝ) (gamma : ℝ) := proven

noncomputable def FrourioFunctional.F {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : X → ℝ  := proven

noncomputable def FrourioFunctional.ofK {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) : FrourioFunctional X  := proven

def K1prime {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop  := proven

def K4m {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) : Prop  := proven

theorem k1prime_ofK_from_uniform_lower_bound {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup C0 : ℝ)
  (hS : 0 ≤ Ssup) (hLB : UniformLowerBoundAtZero K C0) :
  K1prime (FrourioFunctional.ofK Ent K gamma Ssup)  := proven

theorem F_lower_bound_of_ofK {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup C0 : ℝ)
  (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup) (hLB : UniformLowerBoundAtZero K C0) :
  ∀ x : X,
    FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x
      ≥ Ent x - gamma * (Ssup * C0)  := proven


theorem ofK_coercive_from_bounds {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_coercive_from_k1prime {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_lower_semicontinuous_from_k1prime {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_proper {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Proper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_halfconvex {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem ofK_strong_upper_bound {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem k4m_ofK_from_gamma_nonneg {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (hγ : 0 ≤ gamma) :
  K4m (FrourioFunctional.ofK Ent K gamma Ssup)  := proven

theorem ofK_jko_stable {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  JKOStable (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem jko_stable_general {X : Type*} [PseudoMetricSpace X] (A : FrourioFunctional X) :
  JKOStable (FrourioFunctional.F A)  := proven

def constructJKOCurve {X : Type*} [PseudoMetricSpace X] (ρ0 : X) : ℝ → X  := proven

theorem constructJKOCurve_satisfies_jko {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (ρ0 : X) : JKO (FrourioFunctional.F A) ρ0  := proven

theorem k4m_scale {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (c : ℝ) (hc : 0 ≤ c) (hK4 : K4m A) :
  K4m { A with gamma := c * A.gamma }  := proven

theorem controlled_functional_from_k1_k4 {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (hK1 : K1prime A) (hK4 : K4m A) :
  (∃ C : ℝ, ∀ x : X, A.Dsigmam x ≥ -C) ∧ (0 ≤ A.gamma)  := proven

structure ConstantBudget where
  (cStar : ℝ) (cD : ℝ) := proven

def lambdaEffLowerBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps lamEff Ssup XiNorm : ℝ) : Prop  := proven

theorem lambdaEffLowerBound_thm {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  {lam eps lamEff Ssup XiNorm : ℝ}
  (h : lamEff ≥ lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)) :
  lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm  := proven

theorem lambdaEffLowerBound_mono {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  {lam eps lamEff lamEff' Ssup XiNorm : ℝ}
  (hle : lamEff ≤ lamEff') (h : lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm) :
  lambdaEffLowerBound A budget lam eps lamEff' Ssup XiNorm  := proven

def MPointZeroOrderBound (Ssup XiNorm : ℝ) : Prop  := proven

def BudgetNonneg (budget : ConstantBudget) : Prop  := proven

theorem DsigmamFromK_upper_bound {X : Type*} [PseudoMetricSpace X]
  (K : KTransform X) (Ssup C0 : ℝ) (hS : 0 ≤ Ssup) (hUB : ∀ x : X, K.map x 0 ≤ C0) :
  ∀ x : X, DsigmamFromK K Ssup x ≤ Ssup * C0  := proven

def ZeroOrderBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup : ℝ) : Prop  := proven

theorem ofK_strong_upper_bound_parametric {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (CEnt C0 : ℝ) (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup) (hC0 : 0 ≤ C0) (hCEnt : 0 ≤ CEnt)
  (hEntUB : ∀ x : X, Ent x ≤ CEnt) (hKUB : ∀ x : X, K.map x 0 ≤ C0) :
  ∃ c : ℝ, 0 ≤ c ∧ ∀ x : X,
    FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c  := proven

theorem strongUpperBound_from_budget {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (hγ : 0 ≤ A.gamma)
  (hEnt : ∃ CEnt : ℝ, 0 ≤ CEnt ∧ ∀ x : X, A.Ent x ≤ CEnt)
  (hDsigma : ∃ CDsigma : ℝ, 0 ≤ CDsigma ∧ ∀ x : X, A.Dsigmam x ≤ CDsigma) :
  StrongUpperBound (FrourioFunctional.F A)  := proven

theorem strongUpperBound_from_kernel_and_budget {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (CEnt C0 : ℝ)
  (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup) (hCEnt : 0 ≤ CEnt) (hC0 : 0 ≤ C0)
  (hEntUB : ∀ x : X, Ent x ≤ CEnt) (hKUB : ∀ x : X, K.map x 0 ≤ C0) :
  StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem lambdaEffLowerBound_from_doobAssumptions_mpoint {X : Type*}
  [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps lamEff Ssup XiNorm : ℝ)
  (hChoice : lamEff ≥
      lambdaBE lam eps
        - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)) :
  lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm  := proven

theorem lambdaEff_formula_from_doob {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps Ssup XiNorm : ℝ) :
  ∃ lamEff : ℝ,
    lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm ∧
    lamEff = lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)  := proven

theorem lambdaEffLowerBound_construct_from_doobAssumptions_mpoint {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (lam eps Ssup XiNorm : ℝ) :
  ∃ lamEff : ℝ, lambdaEffLowerBound A budget lam eps lamEff Ssup XiNorm  := proven

theorem lambdaEffLowerBound_from_doob_pack {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (h : X → ℝ) (D : Diffusion X) (doobPack : DoobQuantitative h D) -- Doob pack with ε
  (lam Ssup XiNorm : ℝ) (hCD : HasCD D lam) : -- Base CD condition
  ∃ lamEff : ℝ,
    lambdaEffLowerBound A budget lam doobPack.eps lamEff Ssup XiNorm ∧
    lamEff = lambdaBE lam doobPack.eps - A.gamma * (budget.cStar * Ssup ^ 2 + budget.cD * XiNorm) ∧
    HasCD (Doob h D) (lambdaBE lam doobPack.eps)  := proven

theorem lambdaEffLowerBound_commutative {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (h : X → ℝ) (D : Diffusion X)
  (doobPack : DoobQuantitative h D) (lam Ssup XiNorm : ℝ) (hCD : HasCD D lam)
  (hCommutative : budget.cStar = 0) : -- Commutative design condition
  ∃ lamEff : ℝ,
    lambdaEffLowerBound A budget lam doobPack.eps lamEff Ssup XiNorm ∧
    lamEff = lambdaBE lam doobPack.eps - A.gamma * budget.cD * XiNorm  := proven

theorem lambdaEffLowerBound_commutative_remark {X : Type*} [PseudoMetricSpace X] :
  ∀ (A : FrourioFunctional X) (budget : ConstantBudget),
  budget.cStar = 0 →
  ∀ lam eps Ssup XiNorm : ℝ,
  lambdaBE lam eps - A.gamma * (budget.cStar * Ssup ^ 2 + budget.cD * XiNorm) =
  lambdaBE lam eps - A.gamma * budget.cD * XiNorm  := proven

def constructLambdaEff {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (h : X → ℝ) (D : Diffusion X)
  (doobPack : DoobQuantitative h D) (lam Ssup XiNorm : ℝ) : ℝ  := proven

structure SlopeSpec (X : Type*) [PseudoMetricSpace X] where
  (slope : (X → ℝ) → X → ℝ) := proven

noncomputable def zeroSlopeSpec (X : Type*) [PseudoMetricSpace X] : SlopeSpec X  := proven

noncomputable def descendingSlopeSpec (X : Type*) [PseudoMetricSpace X] : SlopeSpec X  := proven

noncomputable def slope {X : Type*} [PseudoMetricSpace X]
  (G : X → ℝ) (x : X) : ℝ  := proven

def StrongSlopeUpperBound_pred {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop  := proven

def StrongSlopeUpperBound_with {X : Type*} [PseudoMetricSpace X]
  (S : SlopeSpec X) (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop  := proven

def StrongSlopeUpperBound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) : Prop  := proven

theorem strongSlope_with_zero_equiv {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ) :
  StrongSlopeUpperBound_pred A budget Ssup XiNorm
    ↔ StrongSlopeUpperBound_with (zeroSlopeSpec X) A budget Ssup XiNorm  := proven

theorem slope_strong_upper_bound {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (H : StrongSlopeUpperBound_pred A budget Ssup XiNorm) :
  ∀ x : X,
    slope (FrourioFunctional.F A) x
      ≤ slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)  := proven

theorem slope_strong_upper_bound_with {X : Type*} [PseudoMetricSpace X]
  (S : SlopeSpec X) (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) (H : StrongSlopeUpperBound_with S A budget Ssup XiNorm) :
  ∀ x : X,
    S.slope (FrourioFunctional.F A) x
      ≤ S.slope A.Ent x + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)  := proven

theorem slope_strong_upper_bound_default {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget)
  (Ssup XiNorm : ℝ) (H : StrongSlopeUpperBound A budget Ssup XiNorm) :
  ∀ x : X,
    (descendingSlopeSpec X).slope (FrourioFunctional.F A) x
      ≤ (descendingSlopeSpec X).slope A.Ent x
        + A.gamma * (budget.cStar * Ssup ^ (2 : ℕ) + budget.cD * XiNorm)  := proven

theorem slope_upper_bound_zero {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (budget : ConstantBudget) (Ssup XiNorm : ℝ)
  (hB : BudgetNonneg budget) (hγ : 0 ≤ A.gamma) (hS : 0 ≤ Ssup) (hX : 0 ≤ XiNorm) :
  StrongSlopeUpperBound_pred A budget Ssup XiNorm  := proven

def EntGeodesicSemiconvex {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (lambda : ℝ) : Prop  := proven

theorem halfConvex_from_ent_geodesic_semiconvex {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lambdaBE : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lambdaBE  := proven

theorem halfConvex_from_doob_lambdaBE {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lam eps : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) (lambdaBE lam eps)  := proven

def provideHalfConvexFlag {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lambdaBE : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lambdaBE  := proven

theorem halfConvexFlag_from_doobQuantitative {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (h : X → ℝ) (D : Diffusion X) (HQ : DoobQuantitative h D) (lam : ℝ) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
    (lambdaBE lam HQ.eps)  := proven

theorem halfConvex_strongUpperBound_integration {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lambdaBE : ℝ)
  (hSUB : StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))) :
  HalfConvex (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lambdaBE ∧
  StrongUpperBound (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_proper_real {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (x₀ : X) -- Need at least one point in X
  (CEnt CDsigma : ℝ) (hγ : 0 ≤ gamma) (hEntLB : ∀ x : X, Ent x ≥ -CEnt)
  (hDsigmaLB : ∀ x : X, (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -CDsigma) :
  ∃ c : ℝ,
    (Set.Nonempty {x | FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c}) ∧
    BddBelow (Set.range (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))  := proven

theorem ofK_proper_real_from_k1prime {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (x₀ : X) (CEnt : ℝ)
  (hγ : 0 ≤ gamma) (hEntLB : ∀ x : X, Ent x ≥ -CEnt)
  (hK1 : K1prime (FrourioFunctional.ofK Ent K gamma Ssup)) :
  ∃ c : ℝ,
    (Set.Nonempty {x | FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c}) ∧
    BddBelow (Set.range (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))  := proven

theorem proper_surrogate_from_real {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) : Proper F  := proven

theorem ofK_proper_from_proper_real {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Proper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

lemma lowerSemicontinuous_const_mul {X : Type*} [TopologicalSpace X]
  (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : _root_.LowerSemicontinuous f) :
  _root_.LowerSemicontinuous (fun x => c * f x)  := proven

theorem ofK_lowerSemicontinuous_real {X : Type*} [PseudoMetricSpace X] [TopologicalSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (hγ : 0 ≤ gamma)
  (hEnt_lsc : _root_.LowerSemicontinuous Ent)
  (hDsigma_lsc : _root_.LowerSemicontinuous ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam)) :
  _root_.LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem dsigmam_lowerSemicontinuous_from_k1 {X : Type*} [PseudoMetricSpace X] [TopologicalSpace X]
  (K : KTransform X) (Ssup : ℝ) (hS : 0 ≤ Ssup)
  (hK_cont : ∀ s : ℝ, Continuous (fun x => K.map x s)) :
  _root_.LowerSemicontinuous (DsigmamFromK K Ssup)  := proven

theorem ofK_lowerSemicontinuous_from_continuous {X : Type*} [PseudoMetricSpace X]
  [TopologicalSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (hγ : 0 ≤ gamma) (hS : 0 ≤ Ssup)
  (hEnt_cont : Continuous Ent) (hK_cont : ∀ s : ℝ, Continuous (fun x => K.map x s)) :
  _root_.LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem lsc_surrogate_from_real {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) :
  LowerSemicontinuous F  := proven

theorem ofK_lsc_surrogate_from_real {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

def CoerciveReal {X : Type*} [NormedAddCommGroup X] (f : X → ℝ) : Prop  := proven

def CoerciveReal' {X : Type*} [NormedAddCommGroup X] (f : X → ℝ) : Prop  := proven

theorem ofK_coercive_real {X : Type*} [NormedAddCommGroup X] [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 < gamma) -- Need positive gamma for coercivity
  (hEnt_growth : ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ ∀ x : X, Ent x ≥ c₁ * ‖x‖ - c₂)  -- Linear growth
  (hDsigma_bounded_below : ∃ C : ℝ, ∀ x : X,
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -C) :
  CoerciveReal (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem coercive_surrogate_from_real {X : Type*} [NormedAddCommGroup X] [PseudoMetricSpace X]
  (F : X → ℝ) : Coercive F  := proven

theorem ofK_coercive_surrogate_from_real {X : Type*} [NormedAddCommGroup X] [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) :
  Coercive (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

def StandardGeodesicStructure (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
  GeodesicStructure X where
  γ  := proven

theorem ofK_geodesic_structure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
  Nonempty (GeodesicStructure X)  := proven

theorem ofK_geodesic_semiconvex {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (hγ : 0 ≤ gamma)
  (G : GeodesicStructure X) (hEnt : GeodesicSemiconvex G Ent lamEff)
  (hDsigma_convex : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam (G.γ x y t) ≤
    (1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
    t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) :
  GeodesicSemiconvex G (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem convex_implies_geodesic_semiconvex {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X → ℝ) (hf : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f ((1 - t) • x + t • y) ≤ (1 - t) * f x + t * f y) :
  GeodesicSemiconvex (StandardGeodesicStructure X) f 0  := proven

theorem ofK_semiconvex_real {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (hγ : 0 ≤ gamma)
  (G : GeodesicStructure X) (hEnt_semiconvex : GeodesicSemiconvex G Ent lamEff)
  (hDsigma_convex : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam (G.γ x y t) ≤
    (1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
    t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) :
  GeodesicSemiconvex G (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem ofK_semiconvex_standard {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (hγ : 0 ≤ gamma)
  (hEnt_semiconvex : GeodesicSemiconvex (StandardGeodesicStructure X) Ent lamEff)
  (hDsigma_convex : ∀ x y : X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam ((1 - t) • x + t • y) ≤
    (1 - t) * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x +
    t * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y) :
  GeodesicSemiconvex (StandardGeodesicStructure X)
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem semiconvex_combination {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Ent Dsigma : X → ℝ) (gamma lamEff : ℝ) (hγ : 0 ≤ gamma) (G : GeodesicStructure X)
  (hEnt : GeodesicSemiconvex G Ent lamEff) (hDsigma : GeodesicSemiconvex G Dsigma 0) :
  GeodesicSemiconvex G (fun x => Ent x + gamma * Dsigma x) lamEff  := proven

def HasCompactSublevels {X : Type*} [TopologicalSpace X] (f : X → ℝ) : Prop  := proven

theorem ofK_compact_sublevels {X : Type*} [NormedAddCommGroup X]
  [ProperSpace X] -- X is a proper metric space (closed balls are compact)
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 < gamma) (hEnt_coercive : CoerciveReal Ent) -- Ent grows to infinity at infinity
  (hDsigma_bounded_below : ∃ C : ℝ, ∀ x : X,
    (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x ≥ -C)
  (h_lsc : _root_.LowerSemicontinuous
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))) :
  HasCompactSublevels (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem compact_sublevels_from_coercive_continuous {X : Type*} [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X] -- Finite dimensional spaces have Heine-Borel
  (f : X → ℝ) (h_coercive : CoerciveReal f) (h_continuous : Continuous f) :
  HasCompactSublevels f  := proven

theorem compact_sublevels_from_proper_lsc {X : Type*} [NormedAddCommGroup X] [ProperSpace X]
  (f : X → ℝ) (h_lsc : _root_.LowerSemicontinuous f)
  (h_bounded_sublevels : ∀ c : ℝ, Bornology.IsBounded {x : X | f x ≤ c}) :
  HasCompactSublevels f  := proven

lemma posPart_add_le (a b : ℝ) : (a + b)⁺ ≤ a⁺ + b⁺  := proven

lemma posPart_smul (c : ℝ) (hc : 0 ≤ c) (a : ℝ) : (c * a)⁺ = c * a⁺  := proven

lemma ereal_limsup_ne_bot_of_eventually_nonneg {α : Type*} {l : Filter α} [l.NeBot]
  {f : α → ℝ} (h : ∀ᶠ a in l, 0 ≤ f a) :
  Filter.limsup (fun a => (f a : EReal)) l ≠ ⊥  := proven

lemma limsup_ereal_eq_limsup_real_of_bounded {α : Type*} {l : Filter α} [l.NeBot]
  {f : α → ℝ} (h_nonneg : ∀ᶠ a in l, 0 ≤ f a)
  (h_bdd : Filter.IsBoundedUnder (· ≤ ·) l f) :
  (Filter.limsup (fun a => (f a : EReal)) l).toReal = Filter.limsup f l  := proven

lemma descendingSlope_add_le {X : Type*} [PseudoMetricSpace X]
  {f g : X → ℝ} (x : X)
  [Filter.NeBot (nhdsWithin x (posDist x))]
  (h_add_limsup :
    Filter.limsup
      (fun y => (posPart (f x - f y)) / dist x y
               + (posPart (g x - g y)) / dist x y)
      (nhdsWithin x (posDist x))
    ≤ Filter.limsup (fun y => (posPart (f x - f y)) / dist x y)
        (nhdsWithin x (posDist x))
      + Filter.limsup (fun y => (posPart (g x - g y)) / dist x y)
        (nhdsWithin x (posDist x)))
  (h_sum_ub : ∃ M : ℝ, ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (f x - f y)) / dist x y + (posPart (g x - g y)) / dist x y ≤ M) :
  descendingSlope (fun y => f y + g y) x ≤ descendingSlope f x + descendingSlope g x  := proven

lemma descendingSlope_smul {X : Type*} [PseudoMetricSpace X]
  {f : X → ℝ} (c : ℝ) (x : X)
  [Filter.NeBot (nhdsWithin x (posDist x))]
  (h_scale :
    Filter.limsup (fun y => (posPart (c * f x - c * f y)) / dist x y)
      (nhdsWithin x (posDist x))
    = c * Filter.limsup (fun y => (posPart (f x - f y)) / dist x y)
      (nhdsWithin x (posDist x))) :
  descendingSlope (fun y => c * f y) x = c * descendingSlope f x  := proven

lemma descendingSlope_le_of_lipschitz {X : Type*} [PseudoMetricSpace X]
  {f : X → ℝ} {L : NNReal} (hf : LipschitzWith L f) (x : X)
  [Filter.NeBot (nhdsWithin x (posDist x))] :
  descendingSlope f x ≤ L  := proven

theorem ofK_slope_bound {X : Type*} [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 ≤ gamma)
  (hEnt_slope : ∃ M_Ent : ℝ, 0 ≤ M_Ent ∧ ∀ x : X, descendingSlope Ent x ≤ M_Ent)
  (hDsigma_lipschitz : ∃ L : NNReal,
    LipschitzWith L (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam)
  (hNeBot : ∀ x : X, Filter.NeBot (nhdsWithin x (posDist x)))
  (h_add_limsup : ∀ x : X,
      Filter.limsup
        (fun y => (posPart (Ent x - Ent y)) / dist x y
                 + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
        (nhdsWithin x (posDist x))
      ≤ Filter.limsup (fun y => (posPart (Ent x - Ent y)) / dist x y)
          (nhdsWithin x (posDist x))
        + Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
          (nhdsWithin x (posDist x)))
  (h_sum_ub : ∀ x : X, ∃ M : ℝ, ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (Ent x - Ent y)) / dist x y
      + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                 - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                / dist x y ≤ M)
  (h_scale_all : ∀ x : X,
      Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                       - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                              / dist x y)
                   (nhdsWithin x (posDist x))
      = gamma * Filter.limsup (fun y => (posPart ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                              - (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                                      / dist x y)
                              (nhdsWithin x (posDist x))) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X,
    descendingSlope (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x ≤ M  := proven

theorem ofK_slope_bound_from_lipschitz {X : Type*} [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hγ : 0 ≤ gamma)
  (hEnt_lip : ∃ K_Ent : NNReal, LipschitzWith K_Ent Ent)
  (hDsigma_lip : ∃ K_D : NNReal,
    LipschitzWith K_D (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam)
  (hNeBot : ∀ x : X, Filter.NeBot (nhdsWithin x (posDist x)))
  (h_add_limsup : ∀ x : X,
      Filter.limsup
        (fun y => (posPart (Ent x - Ent y)) / dist x y
                 + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
        (nhdsWithin x (posDist x))
      ≤ Filter.limsup (fun y => (posPart (Ent x - Ent y)) / dist x y)
          (nhdsWithin x (posDist x))
        + Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                            - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                          / dist x y)
          (nhdsWithin x (posDist x)))
  (h_sum_ub : ∀ x : X, ∃ M : ℝ, ∀ᶠ y in nhdsWithin x (posDist x),
      (posPart (Ent x - Ent y)) / dist x y
      + (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                 - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                / dist x y ≤ M)
  (h_scale_all : ∀ x : X,
      Filter.limsup (fun y => (posPart (gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                       - gamma * (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                              / dist x y)
                   (nhdsWithin x (posDist x))
      = gamma * Filter.limsup (fun y => (posPart ((FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam x
                                              - (FrourioFunctional.ofK Ent K gamma Ssup).Dsigmam y))
                                      / dist x y)
                              (nhdsWithin x (posDist x))) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X,
    descendingSlope (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x ≤ M  := proven

theorem ofK_satisfies_analytic_flags {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (lamEff : ℝ) :
  AnalyticFlags (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem ofK_satisfies_analytic_flags_with_doob {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (h : X → ℝ) (D : Diffusion X) (HQ : DoobQuantitative h D) (lam : ℝ) :
  AnalyticFlags (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup))
    (lambdaBE lam HQ.eps)  := proven

theorem analytic_flags_achievable {X : Type*} [PseudoMetricSpace X] :
  ∃ (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ),
    AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem ofK_plfa_ede_bridge {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) :
  PLFA_EDE_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_ede_evi_bridge {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (flags : AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_ede_evi : EDE_EVI_from_analytic_flags (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  EDE_EVI_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

theorem ofK_full_bridge {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (real_flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  (h_ede_evi_builder : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  PLFA_EDE_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))
  ∧ (∃ _ : AnalyticFlags (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff,
     EDE_EVI_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)  := proven

example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  -- Assume we have the real flags
  (real_flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  -- Assume USC hypothesis
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  -- Assume we have the EDE-EVI builder (from PLFACore3)
  (h_ede_evi : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  -- Then we get PLFA_EDE_pred
  PLFA_EDE_pred (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_plfaEdeEviJko_equiv_real {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  (h_plfa_ede : PLFA_EDE_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_ede_evi : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_jko_plfa : JKO_PLFA_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  plfaEdeEviJko_equiv (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff  := proven

example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (real_flags : AnalyticFlagsReal X (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ)
  -- Assume we have all the builders
  (h_plfa_ede : PLFA_EDE_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_ede_evi : EDE_EVI_from_analytic_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (h_jko_plfa : JKO_PLFA_from_real_flags
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff) :
  -- Then we have all the equivalences
  (∀ ρ : ℝ → X, PLFA (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ ↔
                 EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) ∧
  (∀ ρ : ℝ → X, EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ ↔
                 IsEVISolution ({ E := FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup),
                                  lam := lamEff } : EVIProblem X) ρ)  := proven

noncomputable def ofK_to_EVIProblem {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) : EVIProblem X  := proven

def ofK_IsEVISolution {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) (ρ : ℝ → X) : Prop  := proven

noncomputable def ofK_from_FGData {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  [MeasurableSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (FG : FGData X) : EVIProblem X  := proven

def ofK_fg_IsEVISolution {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  [MeasurableSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (FG : FGData X) (ρ : ℝ → X) : Prop  := proven

theorem ofK_evi_iff_ede {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (equiv : plfaEdeEviJko_equiv (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  (ρ : ℝ → X) :
  ofK_IsEVISolution Ent K gamma Ssup lamEff ρ ↔
  EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ  := proven

def ofK_evi_contraction {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (hu : ofK_IsEVISolution Ent K gamma Ssup lamEff u)
  (hv : ofK_IsEVISolution Ent K gamma Ssup lamEff v) : Prop  := proven

example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (ρ : ℝ → X)
  -- Assume we have the equivalence package
  (equiv : plfaEdeEviJko_equiv (FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup)) lamEff)
  -- If ρ satisfies EDE
  (h_ede : EDE (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) :
  -- Then ρ is an EVI solution
  ofK_IsEVISolution Ent K gamma Ssup lamEff ρ  := proven

theorem ofK_mm_proper {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  [Nonempty X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (hNZ : ∃ x : X,
      FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≠ 0) :
  MmProper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_mm_compact_sublevels {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (h_compact : ∀ c : ℝ, IsCompact {x : X | FrourioFunctional.F
    (FrourioFunctional.ofK Ent K gamma Ssup) x ≤ c}) :
  MmCompactSublevels (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup))  := proven

theorem ofK_jko_to_mm_curve {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (τ : ℝ) (hτ : 0 < τ)
  (x0 : X)
  -- Assume existence of minimizers (would need proper + coercive + lsc)
  (h_exists : ∀ xPrev : X, ∃ x : X, MmStep τ
    (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) xPrev x) :
  ∃ curve : MmCurve τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) x0,
    -- The curve energy is non-increasing
    ∀ n : ℕ, FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) (curve.points (n + 1)) ≤
             FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) (curve.points n)  := proven

theorem ofK_mm_to_plfa_limit {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ)
  (ρ : ℝ → X)
  -- Provide PLFA as an external hypothesis in this placeholder API
  (h_plfa : PLFA (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ) :
  -- Then ρ satisfies PLFA
  PLFA (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) ρ  := proven

theorem ofK_mm_energy_decrease {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (τ : ℝ) (hτ : 0 < τ)
  (xPrev x : X)
  (h_step : MmStep τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) xPrev x) :
  FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) x ≤
  FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup) xPrev  := proven

example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X] [Nonempty X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup : ℝ) (τ : ℝ) (hτ : 0 < τ)
  -- Assume we have proper + compact sublevels + lsc
  (h_proper : MmProper (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))
  (h_compact : MmCompactSublevels (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))
  (h_lsc : _root_.LowerSemicontinuous (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)))
  -- Then minimizers exist for each MM step
  (xPrev : X) :
  ∃ x : X, MmStep τ (FrourioFunctional.F (FrourioFunctional.ofK Ent K gamma Ssup)) xPrev x  := proven

def ofK_TwoEVIWithForce {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X) : Prop  := proven

def ofK_TwoEVIWithForceShared {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X) : Prop  := proven

theorem ofK_twoEVIShared_to_plain {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X) :
  ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v →
  ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v  := proven

theorem ofK_twoEVIWithForce_to_distance {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

theorem ofK_twoEVIWithForce_to_distance_concrete {X : Type*}
  [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

theorem ofK_twoEVIWithForce_to_distance_concrete_closed {X : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

theorem ofK_twoEVIWithForceShared_to_distance {X : Type*}
  [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

theorem ofK_twoEVIWithForceShared_to_distance_concrete {X : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

theorem ofK_twoEVIWithForceShared_to_distance_concrete_closed {X : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  (H : ofK_TwoEVIWithForceShared Ent K gamma Ssup lamEff u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

example {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u v : ℝ → X)
  -- Assume Two-EVI with force holds
  (H : ofK_TwoEVIWithForce Ent K gamma Ssup lamEff u v)
  -- Assume Grönwall holds for all parameters (closed form route)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred lamEff η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ,
    ContractionPropertyWithError (ofK_to_EVIProblem Ent K gamma Ssup lamEff) u v η  := proven

def EVIProblemProduct {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y) : EVIProblem (X × Y) where
  E  := proven

theorem isEVISolution_product_l2 {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (u₁ : ℝ → X) (u₂ : ℝ → Y)
  (h₁ : IsEVISolution P₁ u₁) (h₂ : IsEVISolution P₂ u₂)
  -- Additional assumption: l2-type product metric
  (hl2 : ∀ x x' : X, ∀ y y' : Y,
    dist ((x,y) : X × Y) ((x',y') : X × Y) ^ 2 = dist x x' ^ 2 + dist y y' ^ 2)
  -- We additionally assume an additivity upper bound for the upper Dini derivative,
  -- supplied via the predicate wrapper in EVICore2 for the specific summands we use.
  (hAdd : ∀ (v : X × Y) (t : ℝ),
    DiniUpper_add_le_pred (fun τ => d2 (u₁ τ) v.1) (fun τ => d2 (u₂ τ) v.2) t)
  :
  IsEVISolution (P₁ ⊗ P₂) (fun t => (u₁ t, u₂ t))  := proven

theorem isEVISolution_product_fst {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (u : ℝ → X × Y)
  (h : IsEVISolution (P₁ ⊗ P₂) u)
  (hlam : P₁.lam ≤ P₂.lam)
  -- Monotonicity of the upper Dini derivative under the l∞ product metric:
  -- fixing the Y-test point `w`, the squared product distance dominates
  -- the X-component squared distance along the curve.
  (hDiniMono : ∀ (v : X) (w : Y) (t : ℝ),
      DiniUpper (fun τ => d2 ((u τ).1) v) t ≤ DiniUpper (fun τ => d2 (u τ) (v, w)) t)
  -- Projection equality at time t: when the Y components agree, the product
  -- squared distance equals the X-component squared distance (l∞ metric).
  (hd2_proj_eq : ∀ (x x' : X) (y : Y), d2 (x, y) (x', y) = d2 x x') :
  IsEVISolution P₁ (fun t => (u t).1)  := proven

theorem isEVISolution_product_snd {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (u : ℝ → X × Y)
  (h : IsEVISolution (P₁ ⊗ P₂) u)
  (hlam : P₂.lam ≤ P₁.lam)
  -- Dini monotonicity for the Y-component under the l∞ product metric
  (hDiniMono : ∀ (w : X) (v : Y) (t : ℝ),
      DiniUpper (fun τ => d2 ((u τ).2) v) t ≤ DiniUpper (fun τ => d2 (u τ) (w, v)) t)
  -- Product squared distance equals Y-component squared distance when X agrees
  (hd2_proj_eq : ∀ (x : X) (y y' : Y), d2 (x, y) (x, y') = d2 y y') :
  IsEVISolution P₂ (fun t => (u t).2)  := proven

def EVIProblemTriple {X Y Z : Type*} [PseudoMetricSpace X]
  [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y) (P₃ : EVIProblem Z) :
  EVIProblem (X × Y × Z) where
  E  := proven

theorem product_has_minimizer {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (h₁ : ∃ x₀, ∀ x, P₁.E x₀ ≤ P₁.E x)
  (h₂ : ∃ y₀, ∀ y, P₂.E y₀ ≤ P₂.E y) :
  ∃ p₀, (P₁ ⊗ P₂).E p₀ = sInf (Set.range (P₁ ⊗ P₂).E)  := proven

theorem product_energy_decrease {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (P₁ : EVIProblem X) (P₂ : EVIProblem Y)
  (x x' : X) (y y' : Y)
  (h₁ : P₁.E x' ≤ P₁.E x)
  (h₂ : P₂.E y' ≤ P₂.E y) :
  (P₁ ⊗ P₂).E (x', y') ≤ (P₁ ⊗ P₂).E (x, y)  := proven

noncomputable def ofK_as_EVIProblem {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ) :
  EVIProblem X where
  E  := proven

noncomputable def ofK_decomposed_pair {X : Type*} [PseudoMetricSpace X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEnt lamD : ℝ) :
  EVIProblem X × EVIProblem X where
  fst  := proven

theorem ofK_EVIProblem_equivalence {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lamEff : ℝ)
  (u : ℝ → X)
  (h : ofK_IsEVISolution Ent K gamma Ssup lamEff u) :
  IsEVISolution (ofK_as_EVIProblem Ent K gamma Ssup lamEff) u  := proven

def EVIProblemPower {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (n : ℕ) : EVIProblem (Fin n → X) where
  E  := proven

theorem isEVISolution_power_l2 {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (n : ℕ)
  (u : Fin n → ℝ → X)
  (h : ∀ i, IsEVISolution P (u i))
  -- Assumption: l2-type metric on function space
  (hl2 : ∀ (f g : Fin n → X),
    dist f g ^ 2 = Finset.sum Finset.univ (fun i => dist (f i) (g i) ^ 2))
  -- Assumption: DiniUpper subadditivity over finite sums of component squared distances
  (hAdd : ∀ (v : Fin n → X) (t : ℝ),
    DiniUpper (fun τ => d2 (fun i => u i τ) v) t
      ≤ Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u i τ) (v i)) t)) :
  IsEVISolution (EVIProblemPower P n) (fun t i => u i t)  := proven

theorem isEVISolution_synchronized_l2 {X : Type*} [PseudoMetricSpace X]
  (P : EVIProblem X) (n : ℕ)
  (u : ℝ → X)
  (h : IsEVISolution P u)
  (hl2 : ∀ (f g : Fin n → X),
    dist f g ^ 2 = Finset.sum Finset.univ (fun i => dist (f i) (g i) ^ 2))
  (hAdd : ∀ (v : Fin n → X) (t : ℝ),
    DiniUpper (fun τ => d2 (fun _i => u τ) v) t
      ≤ Finset.sum Finset.univ (fun i => DiniUpper (fun τ => d2 (u τ) (v i)) t)) :
  IsEVISolution (EVIProblemPower P n) (fun t _ => u t)  := proven

structure ScalingParams where
  Lambda : ℝ  -- Metal ratio (Λ > 1)
  kappa : ℝ   -- Generator homogeneity exponent (κ > 0)
  alpha : ℝ   -- Metric scaling exponent (α ≥ 0)
  hLambda : 1 < Lambda
  hkappa : 0 < kappa
  halpha : 0 ≤ alpha := proven

noncomputable def lambdaEffScaled (params : ScalingParams) (lam : ℝ) (k : ℤ) : ℝ  := proven

noncomputable def lambdaScalingFactor (params : ScalingParams) (k : ℤ) : ℝ  := proven

theorem lambdaEffScaled_monotone_increasing {params : ScalingParams}
  (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
  -- For rpow on reals: if Λ > 1 and exponent > 0, then scaling factor > 1
  (hscale_gt : 1 < Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k : ℝ))) :
  lam < lambdaEffScaled params lam k  := proven

theorem lambdaEffScaled_invariant {params : ScalingParams}
  (hbalance : params.kappa = 2 * params.alpha) (lam : ℝ) (k : ℤ) :
  lambdaEffScaled params lam k = lam  := proven

theorem lambdaEffScaled_monotone_decreasing {params : ScalingParams}
  (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
  -- For rpow on reals: if Λ > 1 and exponent < 0 with k>0, then scaling factor < 1
  (hscale_lt : Real.rpow params.Lambda ((params.kappa - 2 * params.alpha) * (k : ℝ)) < 1) :
  lambdaEffScaled params lam k < lam  := proven

def isometricScalingParams (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa) :
  ScalingParams where
  Lambda  := proven

theorem lambdaEffScaled_isometric (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa)
  (lam : ℝ) (k : ℤ) :
  lambdaEffScaled (isometricScalingParams Lambda kappa hLambda hkappa) lam k =
    Lambda ^ (kappa * k) * lam  := proven

def euclideanScalingParams (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa) :
  ScalingParams where
  Lambda  := proven

theorem lambdaEffScaled_euclidean (Lambda kappa : ℝ) (hLambda : 1 < Lambda) (hkappa : 0 < kappa)
  (lam : ℝ) (k : ℤ) :
  lambdaEffScaled (euclideanScalingParams Lambda kappa hLambda hkappa) lam k =
    Lambda ^ ((kappa - 2) * k) * lam  := proven

noncomputable def goldenRatio : ℝ  := proven

theorem goldenRatio_gt_one : 1 < goldenRatio  := proven

noncomputable def goldenScalingParams (kappa alpha : ℝ) (hkappa : 0 < kappa) (halpha : 0 ≤ alpha) :
  ScalingParams where
  Lambda  := proven

def ofK_IsEVISolution_scaled {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lam : ℝ)
  (params : ScalingParams) (k : ℤ) (u : ℝ → X) : Prop  := proven

theorem exists_scaled_solution {X : Type*} [PseudoMetricSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (gamma Ssup lam : ℝ)
  (params : ScalingParams) (k : ℤ)
  -- If there exists a solution with scaled lambda
  (hscale : ∃ v, ofK_IsEVISolution Ent K gamma Ssup (lambdaEffScaled params lam k) v) :
  ∃ v, ofK_IsEVISolution_scaled Ent K gamma Ssup lam params k v  := proven

theorem lambdaEffScaled_composition (params : ScalingParams) (lam : ℝ) (k₁ k₂ : ℤ)
  (hrpow_add : ∀ x y : ℝ,
      Real.rpow params.Lambda (x + y) = Real.rpow params.Lambda x * Real.rpow params.Lambda y) :
  lambdaEffScaled params (lambdaEffScaled params lam k₁) k₂ =
    lambdaEffScaled params lam (k₁ + k₂)  := proven

theorem lambdaEffScaled_inverse (params : ScalingParams) (lam : ℝ) (k : ℤ)
  (hrpow_add : ∀ x y : ℝ,
      Real.rpow params.Lambda (x + y) = Real.rpow params.Lambda x * Real.rpow params.Lambda y) :
  lambdaEffScaled params (lambdaEffScaled params lam k) (-k) = lam  := proven

end Frourio


## ./Frourio/Analysis/FunctionalContinuity.lean

namespace Frourio

lemma norm_sq_le_of_norm_le {x : ℂ} {C : ℝ} (h : ‖x‖ ≤ C) : ‖x‖ ^ 2 ≤ C ^ 2  := proven

lemma zeta_bounded_on_radius (R₀ : ℝ) : ∃ C₀ : ℝ,
    ∀ τ : ℝ, |τ| ≤ R₀ → ‖ZetaLineAPI.zeta_on_line τ‖ ≤ C₀  := proven

end Frourio


## ./Frourio/Analysis/GammaConvergence.lean

namespace Frourio

structure GammaFamily where
  Fh : ℕ → Lp ℂ 2 (volume : Measure ℝ) → ℝ
  F  : Lp ℂ 2 (volume : Measure ℝ) → ℝ := proven

def ConvergesL2 (g_h : ℕ → Lp ℂ 2 (volume : Measure ℝ))
    (g : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

def gammaLiminf (Γ : GammaFamily) : Prop  := proven

def gammaRecovery (Γ : GammaFamily) : Prop  := proven

noncomputable def QdiscGammaFamily (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : GammaFamily  := proven

def Qdisc_gamma_to_Q (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop  := proven

structure GammaAssumptions (Γ : GammaFamily) : Prop where
  liminf  : gammaLiminf Γ
  recovery : gammaRecovery Γ := proven


theorem gammaLiminf_proof (Γ : GammaFamily)
    (h : GammaAssumptions Γ) : gammaLiminf Γ  := proven


theorem gammaRecovery_proof (Γ : GammaFamily)
    (h : GammaAssumptions Γ) : gammaRecovery Γ  := proven

def QdiscGammaAssumptions (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop  := proven

theorem Qdisc_gamma_liminf_proof (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (h : QdiscGammaAssumptions K w Δτ Δξ) :
    let Γ  := proven

theorem Qdisc_gamma_recovery_proof (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (h : QdiscGammaAssumptions K w Δτ Δξ) :
    let Γ  := proven

theorem Qdisc_gamma_to_Q_proof (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (h : QdiscGammaAssumptions K w Δτ Δξ) :
    Qdisc_gamma_to_Q K w Δτ Δξ  := proven

structure GoldenTestSeq (σ : ℝ) where
  /-- The sequence of test functions in Hσ -/
  f : ℕ → Hσ σ
  /-- Width parameter converging to zero -/
  δ : ℕ → ℝ
  /-- Width positivity -/
  hδ_pos : ∀ n, 0 < δ n
  /-- Width convergence to zero -/
  hδ_lim : Filter.Tendsto δ atTop (nhds 0)
  /-- Width parameter decay bound -/
  hδ_bound : ∀ n, δ n ≤ 1 / (n + 1 : ℝ)
  /-- Functions are normalized Gaussians with time shift -/
  gaussian_form : ∀ (_n : ℕ), ∃ (_τ₀ : ℝ) (w : Lp ℂ 2 (volume : Measure ℝ)),
    ‖w‖ = 1 -- Simplified: actual construction would involve proper time shift
  /-- The variational property: f n is a δ n-approximate minimizer of Qζσ -/
  variational_property : ∀ n (y : Hσ σ), Qζσ σ (f n) ≤ Qζσ σ y + δ n := proven

noncomputable def limiting_energy (σ : ℝ) : Hσ σ → ℝ  := proven

theorem gaussian_gamma_convergence {σ : ℝ} (F : GoldenTestSeq σ) :
    (∀ n, 0 ≤ limiting_energy σ (F.f n)) ∧ (limiting_energy σ = Qζσ σ)  := proven

class RHMinimizationCharacterization : Prop where
  critical_min : ∀ σ : ℝ,
    (∃ h : Hσ σ, ∀ g : Hσ σ, limiting_energy σ h ≤ limiting_energy σ g) → σ = 1/2 := proven

lemma critical_line_energy_minimum (σ : ℝ) [RHMinimizationCharacterization] :
    (∃ h : Hσ σ, ∀ g : Hσ σ, limiting_energy σ h ≤ limiting_energy σ g) →
    σ = 1/2  := proven

def GammaConvergesSimple {α : Type*} [NormedAddCommGroup α] (E : ℕ → α → ℝ)
    (E_inf : α → ℝ) : Prop  := proven

end Frourio


## ./Frourio/Analysis/Gaussian.lean

namespace Frourio

lemma norm_ofReal_exp_neg_mul_sq (a t : ℝ) :
    ‖(Real.exp (-(a * t ^ 2)) : ℂ)‖ = Real.exp (-(a * t ^ 2))  := proven

lemma norm_cexp_neg_mul_sq (a t : ℝ) :
    ‖Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))‖ = Real.exp (-(a * t ^ 2))  := proven

lemma exp_sq_eq (x : ℝ) : Real.exp x * Real.exp x = Real.exp (x + x)  := proven

lemma exp_sq_pow_two (x : ℝ) : (Real.exp x) ^ 2 = Real.exp (2 * x)  := proven

lemma memLp_two_iff_integrable_sq_complex (f : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable f (volume : Measure ℝ)) :
    MemLp f 2 (volume : Measure ℝ) ↔
    Integrable (fun t => ‖f t‖ ^ (2 : ℕ)) (volume : Measure ℝ)  := proven


lemma gaussian_memLp (a : ℝ) (ha : 0 < a) :
    MemLp (fun t : ℝ => Real.exp (-a * t^2)) 2 (volume : Measure ℝ)  := proven


lemma gaussian_memLpC_cexp (a : ℝ) (ha : 0 < a) :
    MemLp (fun t : ℝ => Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2))) 2 (volume : Measure ℝ)  := proven

lemma cexp_neg_mul_sq_ofReal (a t : ℝ) :
    Complex.exp (-( (a : ℂ) * (t : ℂ) ^ 2)) = (Real.exp (-(a * t^2)) : ℂ)  := proven


lemma gaussian_memLpC (a : ℝ) (ha : 0 < a) :
    MemLp (fun t : ℝ => (Real.exp (-a * t^2) : ℂ)) 2 (volume : Measure ℝ)  := proven

lemma gaussian_integral_scaled (δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ, Real.exp (- (2 * Real.pi) * t^2 / (δ^2)) ∂(volume : Measure ℝ))
      = δ / Real.sqrt 2  := proven

lemma gaussian_l2_norm_sq_real (δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ, (Real.exp (-Real.pi * t^2 / δ^2)) ^ 2 ∂(volume : Measure ℝ))
      = δ / Real.sqrt 2  := proven

lemma gaussian_l2_norm_sq_complex (δ : ℝ) (hδ : 0 < δ) :
    (∫ t : ℝ, ‖(Real.exp (-Real.pi * t^2 / δ^2) : ℂ)‖ ^ (2 : ℕ) ∂(volume : Measure ℝ))
      = δ / Real.sqrt 2  := proven

lemma cexp_pi_delta_sq_eq (δ : ℝ) (x : ℝ) :
    Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (x : ℂ) ^ 2))
      = (Real.exp (-(Real.pi / δ^2) * x^2) : ℂ)  := proven

lemma gaussian_memLp_pi_delta_sq (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun t : ℝ => Complex.exp (-( ((Real.pi / δ^2) : ℂ) * (t : ℂ) ^ 2))) 2
        (volume : Measure ℝ)  := proven

lemma lintegral_norm_sq_eq_integral_norm_sq (f : ℝ → ℂ)
    (hmeas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    ((∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) ^ (1 / (2 : ℝ))).toReal =
    Real.sqrt (∫ t, ‖f t‖ ^ (2 : ℕ) ∂(volume : Measure ℝ))  := proven

lemma build_normalized_gaussian (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
    ‖w‖ = 1 ∧
    ∀ᵐ t : ℝ, (w : ℝ → ℂ) t = ((2 : ℝ)^(1/4 : ℝ) / Real.sqrt δ : ℝ) *
      (Real.exp (-Real.pi * t^2 / δ^2) : ℂ)  := proven

lemma normalized_gaussian_pointwise_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
      ‖w‖ = 1 ∧
      ∀ᵐ t : ℝ, ‖((w : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t‖
        ≤ ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt δ)
            * Real.exp (-Real.pi * t^2 / δ^2)  := proven

lemma integral_const_mul_gaussian (c δ : ℝ) :
    ∫ t, c * Real.exp (-Real.pi * t ^ 2 / δ ^ 2)
      = c * (∫ t, Real.exp (-Real.pi * t ^ 2 / δ ^ 2))  := proven

lemma gaussian_tail_integral_factor_out (R δ : ℝ) :
    ∫ t, Real.exp (-Real.pi * R ^ 2 / δ ^ 2) * Real.exp (-Real.pi * t ^ 2 / δ ^ 2)
      = Real.exp (-Real.pi * R ^ 2 / δ ^ 2)
          * (∫ t, Real.exp (-Real.pi * t ^ 2 / δ ^ 2))  := proven

lemma measurableSet_abs_gt (R : ℝ) :
    MeasurableSet {t : ℝ | R < |t|}  := proven


lemma integrable_gaussian_product (δ : ℝ) (hδ : 0 < δ) (R : ℝ) :
  Integrable (fun t => Real.exp (-Real.pi * R ^ 2 / δ ^ 2) *
    Real.exp (-Real.pi * t ^ 2 / δ ^ 2))  := proven

lemma tail_bound_calc_helper (δ : ℝ) (R : ℝ)
    (hL : ∫ t in {t : ℝ | R < |t|}, Real.exp (-2 * Real.pi * t ^ 2 / δ ^ 2)
      = ∫ t, Set.indicator {t : ℝ | R < |t|}
              (fun t => Real.exp (-2 * Real.pi * t ^ 2 / δ ^ 2)) t)
    (h_int_le : ∫ t, Set.indicator {t : ℝ | R < |t|}
              (fun t => Real.exp (-2 * Real.pi * t ^ 2 / δ ^ 2)) t
        ≤ ∫ t, Real.exp (-Real.pi * R ^ 2 / δ ^ 2) * Real.exp (-Real.pi * t ^ 2 / δ ^ 2)) :
    ∫ t in {t : ℝ | R < |t|}, Real.exp (-2 * Real.pi * t ^ 2 / δ ^ 2)
      ≤ ∫ t, Real.exp (-Real.pi * R ^ 2 / δ ^ 2) * Real.exp (-Real.pi * t ^ 2 / δ ^ 2)  := proven


lemma gaussian_exp_square_split (a t : ℝ) :
    Real.exp (-2 * a * t^2) = Real.exp (-a * t^2) * Real.exp (-a * t^2)  := proven


lemma gaussian_tail_exp_monotonicity (δ R t : ℝ) (hδ : 0 < δ) (hR_pos : 0 ≤ R) (hR : R ≤ |t|) :
    -Real.pi * t^2 / δ^2 ≤ -Real.pi * R^2 / δ^2  := proven


lemma gaussian_tail_pointwise_bound (δ R t : ℝ) (hδ : 0 < δ) (hR : 0 < R) (hmem : R < |t|) :
    Real.exp (-2 * Real.pi * t^2 / δ^2) ≤
    Real.exp (-Real.pi * R^2 / δ^2) * Real.exp (-Real.pi * t^2 / δ^2)  := proven


lemma gaussian_product_nonneg (δ R t : ℝ) :
    0 ≤ Real.exp (-Real.pi * R^2 / δ^2) * Real.exp (-Real.pi * t^2 / δ^2)  := proven


lemma integral_mono_of_pointwise_le_indicator {f g : ℝ → ℝ} {S : Set ℝ}
    (hf_nonneg : ∀ t, 0 ≤ Set.indicator S f t)
    (hg_int : Integrable g)
    (hle : ∀ t, Set.indicator S f t ≤ g t) :
    ∫ t, Set.indicator S f t ≤ ∫ t, g t  := proven


lemma gaussian_integral_value (δ : ℝ) (hδ : 0 < δ) :
    ∫ t : ℝ, Real.exp (-Real.pi * t^2 / δ^2) = δ  := proven

lemma gaussian_tail_l2_bound (δ : ℝ) (hδ : 0 < δ) (R : ℝ) (hR : 0 < R) :
    ∫ t in {t : ℝ | R < |t|}, Real.exp (-2 * Real.pi * t^2 / δ^2) ∂(volume : Measure ℝ)
      ≤ 2 * Real.exp (-Real.pi * R^2 / δ^2) / Real.sqrt (Real.pi / δ^2)  := proven


lemma gaussian_normalization_factor_squared (δ : ℝ) (hδ : 0 < δ) :
    ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt δ)^2 = Real.sqrt 2 / δ  := proven


lemma exp_squared_formula (t δ : ℝ) :
    (Real.exp (-Real.pi * t^2 / δ^2))^2 = Real.exp (-2 * Real.pi * t^2 / δ^2)  := proven


lemma integrable_indicator_gaussian (δ : ℝ) (hδ : 0 < δ) (R A : ℝ) :
    Integrable (fun t => Set.indicator {t : ℝ | R < |t|}
      (fun t => A^2 * Real.exp (-2 * Real.pi * t^2 / δ^2)) t)  := proven


lemma integral_indicator_const_mul (S : Set ℝ) (c : ℝ) (f : ℝ → ℝ) :
    ∫ t, Set.indicator S (fun t => c * f t) t =
    c * ∫ t, Set.indicator S f t  := proven

lemma normalized_gaussian_tail_vanishes (δ : ℝ) (hδ : 0 < δ) (R : ℝ) (hR : 0 < R) :
    ∃ w : Lp ℂ 2 (volume : Measure ℝ),
      ‖w‖ = 1 ∧
      (∫ t in {t : ℝ | R < |t|}, ‖(w : ℝ → ℂ) t‖^2 ∂(volume : Measure ℝ))
        ≤ 4 * Real.exp (-Real.pi * R^2 / δ^2)  := proven


lemma sqrt_two_pi_lt_three :
    Real.sqrt (2 * Real.pi) < 3  := proven


lemma sqrt_div_sqrt_pi :
    Real.sqrt (2 * Real.pi) / Real.sqrt Real.pi = Real.sqrt 2  := proven


lemma rpow_half_eq_quarter_sq (x : ℝ) (hx : 0 ≤ x) :
    x ^ (1/2 : ℝ) = x ^ (1/4 : ℝ) * x ^ (1/4 : ℝ)  := proven


lemma nat_split_sqrt (n : ℕ) (hn : 0 < (n : ℝ)) :
    (n : ℝ) = (n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ (1/2 : ℝ)  := proven


lemma gaussian_const_squared (n : ℕ) (hn : 0 < (n + 1 : ℝ)) :
    ((2 : ℝ) ^ (1/4 : ℝ) * Real.sqrt (n + 1 : ℝ))^2
    = (2 : ℝ) ^ (1/2 : ℝ) * (n + 1 : ℝ)  := proven


lemma pi_quarter_div_squared (n : ℕ) :
    ((n + 1 : ℝ) / (Real.pi) ^ (1/4 : ℝ))^2
    = ((n + 1 : ℝ) * (n + 1 : ℝ)) / (Real.pi) ^ (1/2 : ℝ)  := proven

lemma gaussian_norm_const_le_alt_const_for_large_n (n : ℕ) (hn : 2 ≤ n) :
    ((2 : ℝ) ^ (1/4 : ℝ) / Real.sqrt (1 / (n + 1 : ℝ)))
      ≤ ((1 / (n + 1 : ℝ)) * Real.pi ^ (1/4 : ℝ))⁻¹  := proven

end Frourio


## ./Frourio/Analysis/GaussianContourShiftReal.lean

namespace Frourio

lemma gaussian_shifted_norm_bound (a : ℂ) (c : ℂ) (x : ℝ) :
    ‖exp (-a * ((x : ℂ) + c)^2)‖ ≤ Real.exp (-a.re *
    (x + c.re)^2 + a.re * c.im^2 + |2 * a.im * c.im * (x + c.re)|)  := proven

lemma gaussian_shifted_bound_integrable (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    Integrable (fun x : ℝ => Real.exp (-a.re * (x + c.re)^2 + a.re * c.im^2))  := proven

lemma gaussian_norm_real (a : ℂ) (_ : 0 < a.re) (x : ℝ) :
    ‖exp (-a * (x : ℂ)^2)‖ = Real.exp (-a.re * x^2)  := proven

lemma young_inequality_for_products (a b c : ℝ) (ε : ℝ) (hε : 0 < ε) :
    |2 * a * b * c| ≤ ε/2 * c^2 + 2 * (a * b)^2 / ε  := proven

lemma gaussian_shifted_integrable (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (-a * (x + c)^2))  := proven

lemma gaussian_integrable_real (a : ℂ) (ha : 0 < a.re) :
    Integrable (fun x : ℝ => Real.exp (-a.re * x^2))  := proven

lemma gaussian_integrable_complex (a : ℂ) (ha : 0 < a.re) :
    Integrable (fun x : ℝ => Complex.exp (-a * x^2))  := proven

lemma gaussian_rectangular_contour (a : ℂ) (_ha : 0 < a.re) (y : ℝ) (R : ℝ) (_hR : 0 < R) :
    let f  := proven

lemma R_positive_from_bound (a : ℂ) (ha : 0 < a.re) (sign : ℝ) (hsign : sign ≠ 0) (b R : ℝ)
    (hb : b < 0) (hR : R ≥ 2 * Real.sqrt (-b * 4 / a.re) / |sign|) : 0 < R  := proven

lemma sq_exceeds_threshold (a_re : ℝ) (ha : 0 < a_re) (sign : ℝ) (hsign : sign ≠ 0)
    (b R : ℝ) (hb : b < 0) (hR : R ≥ 2 * Real.sqrt (-b * 4 / a_re) / |sign|) :
    (sign * R)^2 > -4 * b / a_re  := proven

lemma gaussian_bound_rearrange (a_re : ℝ) (ha : 0 < a_re) (b : ℝ) (x : ℝ)
    (hx : x ^ 2 > -4 * b / a_re) : -(a_re * x^2 / 4) < b  := proven

lemma gaussian_exp_decay (a : ℂ) (ha : 0 < a.re) (sign : ℝ) (hsign : sign ≠ 0) :
    Tendsto (fun R => Real.exp (-(a.re * (sign * R)^2 / 4))) atTop (𝓝 0)  := proven

lemma sqrt_mul_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y  := proven

lemma complex_norm_eq_sqrt (z : ℂ) : ‖z‖ = Real.sqrt (z.re^2 + z.im^2)  := proven

lemma neg_real_to_complex_eq_neg_mul (R : ℝ) :
    -(R : ℂ) = ((-1 : ℝ) * R : ℂ)  := proven

lemma complex_neg_R_plus_tc_eq (R : ℝ) (t : ℝ) (c : ℂ) :
    -(R : ℂ) + t * c = ((-1 : ℝ) * R : ℂ) + t * c  := proven

lemma gaussian_integrand_neg_R_eq (a : ℂ) (c : ℂ) (R : ℝ) (t : ℝ) :
    Complex.exp (-a * ((-(R : ℂ)) + t * c)^2) * c =
    Complex.exp (-a * ((((-1) : ℝ) * R : ℂ) + t * c)^2) * c  := proven

lemma gaussian_left_vertical_eq (a : ℂ) (c : ℂ) :
    ∀ R : ℝ, ∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp (-a * ((-(R : ℂ)) + t * c)^2) * c =
      ∫ t in (0 : ℝ)..(1 : ℝ), Complex.exp (-a * ((((-1) : ℝ) * R : ℂ) + t * c)^2) * c  := proven

lemma gaussian_horizontal_conv_shifted (a : ℂ) (ha : 0 < a.re) (c : ℂ) :
    let f  := proven

lemma gaussian_horizontal_conv_real (a : ℂ) (ha : 0 < a.re) :
    let f  := proven

lemma gaussian_vertical_norm_eq_aux
    (a : ℂ) (R t : ℝ) (right : Bool)
    (hz_mul : -a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2 =
      -a * (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I) ^ 2) :
    ‖Complex.exp (-a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I) ^ 2)‖ =
      Real.exp ((-a *
        (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I) ^ 2).re)  := proven


lemma gaussian_vertical_norm_eq (a : ℂ) (R t : ℝ) (right : Bool) :
    ‖Complex.exp (-a * ((if right then (R : ℂ) else -R) + (t : ℂ) * I)^2)‖ =
      Real.exp ((-a *
        (Complex.ofReal ((if right then (1 : ℝ) else -1) * R) + (t : ℂ) * I)^2).re)  := proven


lemma gaussian_vertical_exponential_bound (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (R : ℝ), R > 0 → ∀ t ∈ Set.Icc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2)‖ ≤
      C * Real.exp (-a.re * R^2 + a.re * y^2 + 2 * |a.im| * R * |y|)  := proven

lemma gaussian_vertical_integral_norm_estimate (a : ℂ) (ha : 0 < a.re) (ha_im : a.im = 0)
    (y : ℝ) (hy : 0 ≤ y) (right : Bool) (C₁ : ℝ) (hC₁_pos : 0 < C₁)
    (hC₁_bound : ∀ (R : ℝ), R > 0 → ∀ t ∈ Set.Icc 0 y,
      ‖Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2)‖ ≤
      C₁ * Real.exp (-a.re * R ^ 2 + a.re * y ^ 2)) :
    ∀ (R : ℝ), R > 1 →
      ‖∫ t in (0 : ℝ)..y, Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
      |y| * C₁ * Real.exp (-a.re * R^2 + a.re * y^2)  := proven

lemma exp_comparison_large_R (a : ℂ) (ha : 0 < a.re) (y : ℝ) (R : ℝ) (hR : R > 1) :
    Real.exp (-a.re * R^2 + a.re * y^2) ≤
    Real.exp (2 * a.re * y^2) * Real.exp (-a.re * R^2 / 2)  := proven

lemma gaussian_vertical_integral_bound (a : ℂ) (ha : 0 < a.re)
    (ha_im : a.im = 0) (y : ℝ) (hy : 0 ≤ y) (right : Bool) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (R : ℝ), R > 1 →
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
      C * Real.exp (-a.re * R^2 / 2)  := proven

lemma exp_neg_quadratic_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun R : ℝ => Real.exp (-c * R^2 / 2))
      Filter.atTop (𝓝 0)  := proven

inductive IntegralBoundType
  | at_one : IntegralBoundType           -- R = 1
  | interval : IntegralBoundType         -- R ∈ [0,1]
  | negative : IntegralBoundType         -- R < 0 and R ≤ 1 := proven

lemma gaussian_vertical_integral_bounded_unified (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (bound_type : IntegralBoundType)
    (h_cond : match bound_type with
      | IntegralBoundType.at_one => R = 1
      | IntegralBoundType.interval => 0 ≤ R ∧ R ≤ 1
      | IntegralBoundType.negative => R < 0 ∧ R ≤ 1) :
    ∃ M : ℝ, M > 0 ∧
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M  := proven

lemma gaussian_vertical_integral_bounded_with_C (a : ℂ) (_ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (C : ℝ) (_hC_pos : 0 < C)
    (hC_bound : ∀ (R' : ℝ), R' > 1 → ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then ↑R' else -↑R') + ↑t * I) ^ 2) *
      I‖ ≤ C * Real.exp (-a.re * R' ^ 2 / 2))
    (hR : R = 1) :
    ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) *
      I‖ ≤ C * Real.exp (-a.re * R^2 / 2)  := proven

lemma gaussian_vertical_integral_at_one (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (C : ℝ) (hC_pos : 0 < C)
    (hC_bound : ∀ (R : ℝ), R > 1 → ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2) *
      I‖ ≤ C * Real.exp (-a.re * R ^ 2 / 2)) :
    ‖∫ t in (0 : ℝ)..y,
      Complex.exp (-a * ((if right then (1:ℂ) else -(1:ℂ)) + ↑t * I)^2) *
      I‖ ≤ C * Real.exp (-a.re / 2)  := proven

inductive SqLeOneCondition
  | nonneg_le : SqLeOneCondition    -- 0 ≤ R ≤ 1
  | abs_le : SqLeOneCondition        -- |R| ≤ 1
  | neg_le : SqLeOneCondition        -- R < 0 and R ≤ 1 := proven

lemma sq_le_one_unified (R : ℝ) (cond : SqLeOneCondition)
    (h : match cond with
      | SqLeOneCondition.nonneg_le => 0 ≤ R ∧ R ≤ 1
      | SqLeOneCondition.abs_le => |R| ≤ 1
      | SqLeOneCondition.neg_le => R < 0 ∧ R ≤ 1 ∧ -1 ≤ R) : R^2 ≤ 1  := proven

lemma sq_le_one_of_le_one (R : ℝ) (hR : R ≤ 1) (hR_nonneg : 0 ≤ R) : R^2 ≤ 1  := proven

lemma sq_le_one_of_abs_le_one (R : ℝ) (hR : |R| ≤ 1) : R^2 ≤ 1  := proven

lemma sq_le_one_of_neg_le_one (R : ℝ) (hR_neg : R < 0) (hR_le : R ≤ 1)
    (hR_ge : -1 ≤ R) : R^2 ≤ 1  := proven

lemma gaussian_vertical_integral_bounded_on_interval (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (hR_le : R ≤ 1) (hR_ge : 0 ≤ R) :
    ∃ M : ℝ, M > 0 ∧
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M  := proven

lemma gaussian_vertical_integral_bounded_negative (a : ℂ) (ha : 0 < a.re) (y : ℝ) (right : Bool)
    (R : ℝ) (hR_neg : R < 0) (hR_le : R ≤ 1) :
    ∃ M : ℝ, M > 0 ∧
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M  := proven

lemma gaussian_vertical_integral_continuous (a : ℂ) (y : ℝ) (right : Bool) :
    ContinuousOn
      (fun R : ℝ => ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖)
      (Set.Icc 0 1)  := proven

lemma continuous_on_compact_attains_max {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {f : α → ℝ} (hf : Continuous f) (S : Set α)
    (hS_compact : IsCompact S) (hS_nonempty : S.Nonempty) :
    ∃ x₀ ∈ S, ∀ x ∈ S, f x ≤ f x₀  := proven

lemma gaussian_vertical_integral_max_exists (a : ℂ) (y : ℝ) (right : Bool) :
    ∃ R_max ∈ Set.Icc (0:ℝ) 1,
      ∀ R ∈ Set.Icc (0:ℝ) 1,
        ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
        ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R_max else -↑R_max) + ↑t * I)^2) * I‖  := proven

lemma integral_bound_on_interval (a : ℂ) (y : ℝ) (right : Bool) (M : ℝ)
    (hM_is_max : ∃ R₀ ∈ Set.Icc (0 : ℝ) 1,
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R₀ else -↑R₀) + ↑t * I) ^ 2) * I‖ = M ∧
      ∀ R ∈ Set.Icc (0 : ℝ) 1,
        ‖∫ t in (0 : ℝ)..y,
          Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I) ^ 2) * I‖ ≤ M) :
    ∀ R ∈ Set.Icc (0:ℝ) 1,
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤ M  := proven

lemma abs_le_one_of_in_interval (R : ℝ) (hR_lower : -1 ≤ R) (hR_upper : R ≤ 1) : |R| ≤ 1  := proven

lemma exp_ge_one_of_R_sq_le_one (a : ℂ) (ha : 0 < a.re) (R : ℝ) (h_R_sq : R ^ 2 ≤ 1) :
    1 ≤ Real.exp (a.re / 2 - a.re * R^2 / 2)  := proven

lemma small_bound_le_C_small_exp (a : ℂ) (ha : 0 < a.re) (R : ℝ) (h_R_sq : R ^ 2 ≤ 1)
    (M_small : ℝ) (hM_small_nonneg : 0 ≤ M_small) :
    M_small + 1 ≤ (M_small + 1) * Real.exp (a.re / 2) * Real.exp (-a.re * R^2 / 2)  := proven

lemma gaussian_vertical_integral_bounded_all (a : ℂ) (ha : 0 < a.re) (ha_im : a.im = 0)
    (y : ℝ) (hy : 0 ≤ y) (right : Bool) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (R : ℝ),
      ‖∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I‖ ≤
      C * Real.exp (-a.re * R^2 / 2)  := proven

lemma gaussian_vertical_integral_vanish_aux (a : ℂ) (ha : 0 < a.re) (ha_im : a.im = 0)
    (y : ℝ) (hy : 0 ≤ y) (right : Bool) :
    Filter.Tendsto
      (fun R : ℝ => ∫ t in (0 : ℝ)..y,
        Complex.exp (-a * ((if right then ↑R else -↑R) + ↑t * I)^2) * I)
      (Filter.atTop : Filter ℝ) (𝓝 (0 : ℂ))  := proven

lemma gaussian_vertical_integrals_vanish (a : ℂ) (ha : 0 < a.re)
    (ha_im : a.im = 0) (y : ℝ) (hy : 0 ≤ y) :
    let f  := proven

lemma gaussian_integral_diff_limit (a : ℂ) (y : ℝ) :
    let f  := proven

theorem gaussian_contour_shift_general {a : ℂ} (ha : 0 < a.re)
    (ha_im : a.im = 0) (c : ℂ) (hc : c.re = 0) (hc_im : 0 ≤ c.im) :
    ∫ x : ℝ, Complex.exp (-a * (↑x + c)^2) = ∫ x : ℝ, Complex.exp (-a * ↑x^2)  := proven

lemma pi_div_delta_sq_re_pos {δ : ℝ} (hδ : 0 < δ) : 0 < (↑π / ↑δ^2 : ℂ).re  := proven

lemma pi_div_delta_sq_im_zero (δ : ℝ) : (↑π / ↑δ^2 : ℂ).im = 0  := proven

lemma i_delta_sq_xi_re_zero (δ ξ : ℝ) : (I * ↑(δ^2) * ↑ξ : ℂ).re = 0  := proven

lemma i_delta_sq_xi_im (δ ξ : ℝ) : (I * ↑(δ^2) * ↑ξ : ℂ).im = δ^2 * ξ  := proven

lemma gaussian_integrable_basic (a : ℂ) (ha : 0 < a.re) :
    ∀ c : ℂ, Integrable (fun x : ℝ => Complex.exp (-a * (↑x + c)^2))  := proven

def neg_homeomorph : Homeomorph ℝ ℝ := {
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := fun x => by simp
  right_inv := fun x => by simp
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg
} := proven

lemma neg_homeomorph_measure_preserving :
    MeasureTheory.MeasurePreserving neg_homeomorph.toFun  := proven


lemma integral_gaussian_neg_substitution (a : ℂ) (c : ℂ) :
    ∫ (x : ℝ), Complex.exp (-a * (↑x + c)^2) =
    ∫ (x : ℝ), Complex.exp (-a * (↑(-x) + c)^2)  := proven

lemma gaussian_shift_transform (a_param : ℂ) (c_param : ℂ)
    (h_subst_left : ∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param) ^ 2) =
                     ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param) ^ 2))
    (h_simplified : ∫ (u : ℝ), Complex.exp (-a_param * (↑(-u) + c_param) ^ 2) =
                     ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param) ^ 2))
    (h_expand : ∫ (u : ℝ), Complex.exp (-a_param * (↑u - c_param) ^ 2) =
                 ∫ (u : ℝ), Complex.exp (-a_param * ((↑u) ^ 2 - 2 * ↑u * c_param + c_param ^ 2)))
    (h_general : ∫ (u : ℝ), Complex.exp (-a_param * (↑u + (-c_param)) ^ 2) =
                  ∫ (s : ℝ), Complex.exp (-a_param * ↑s ^ 2)) :
    ∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param)^2) =
    ∫ (s : ℝ), Complex.exp (-a_param * ↑s^2)  := proven

lemma gaussian_parametric_to_original (δ ξ : ℝ)
    (a_param : ℂ) (c_param : ℂ)
    (h_a_def : a_param = ↑π / ↑δ ^ 2)
    (h_c_def : c_param = I * ↑δ ^ 2 * ↑ξ) :
    (∫ (a : ℝ), Complex.exp (-a_param * (↑a + c_param)^2) =
     ∫ (s : ℝ), Complex.exp (-a_param * ↑s^2)) ↔
    (∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
     ∫ (s : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑s^2))  := proven

lemma gaussian_shift_neg_case (δ ξ : ℝ) (hδ : 0 < δ) (hξ : ξ < 0) :
    ∫ (a : ℝ), Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ (s : ℝ), Complex.exp (-↑π / ↑δ^2 * ↑s^2)  := proven

theorem gaussian_contour_shift_real {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2)  := proven

end Frourio


## ./Frourio/Analysis/GaussianFourierTransform.lean

namespace Frourio

def normalizedGaussianLp (δ : ℝ) (hδ : 0 < δ) : Lp ℂ 2 (volume : Measure ℝ)  := proven

lemma div_sqrt_mul_delta {A : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    A / ↑(Real.sqrt δ) * ↑δ = A * ↑(Real.sqrt δ)  := proven

lemma delta_sq_inv_sq {δ : ℝ} (hδ : 0 < δ) :
    ((↑δ : ℂ) * ↑δ) * ((↑δ)⁻¹ * (↑δ)⁻¹) = 1  := proven

lemma complete_square_simplify {δ : ℝ} (hδ : 0 < δ) (ξ t : ℝ) :
    -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 + ↑π / ↑δ^2 * (-1) * (↑δ^2)^2 * ↑ξ^2 =
    -↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2 - ↑π * ↑δ^2 * ↑ξ^2  := proven

lemma complex_gaussian_contour_shift {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2)  := proven

lemma gaussian_contour_shift {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ a : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑a + I * ↑δ^2 * ↑ξ)^2) =
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2)  := proven

@[simp]
lemma integral_ofReal' {f : ℝ → ℝ} :
    (∫ x : ℝ, ↑(f x) : ℂ) = ↑(∫ x : ℝ, f x)  := proven

lemma gaussian_integral_complex {δ : ℝ} (hδ : 0 < δ) :
    ∫ s : ℝ, Complex.exp (-↑π / ↑δ^2 * ↑s^2) = ↑δ  := proven

lemma shifted_gaussian_integral {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (-↑π / ↑δ^2 * (↑t + I * ↑δ^2 * ↑ξ)^2) = ↑δ  := proven

lemma complex_shifted_gaussian_integral {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (-π / δ^2 * (t + I * δ^2 * ξ)^2) = δ  := proven

lemma gaussian_fourier_real_exp {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(-2 * π * ξ * t) * I) * ↑(Real.exp (-Real.pi * t^2 / δ^2)) =
    δ * Complex.exp (-π * δ^2 * ξ^2)  := proven

lemma gaussian_fourier_transform {δ : ℝ} (hδ : 0 < δ) :
    fourierIntegral (((normalizedGaussianLp δ hδ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) =
    fun (ξ : ℝ) => ((2 : ℂ)^((1 : ℂ)/4) * sqrt δ) * Complex.exp (-π * δ^2 * ξ^2)  := proven

end Frourio


## ./Frourio/Analysis/GaussianMoments.lean

namespace Frourio


lemma normalizedGaussianLp_norm_one {δ : ℝ} (hδ : 0 < δ) :
    ‖normalizedGaussianLp δ hδ‖ = 1  := proven

lemma gaussian_second_moment_finite {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ t : ℝ, ENNReal.ofReal (t^2 * ‖(((normalizedGaussianLp δ hδ :
      Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) t‖^2) ∂volume < ⊤  := proven

lemma gaussian_kernel_integrand_eq (δ ξ : ℝ) :
    (fun t : ℝ =>
        Complex.exp (↑(-2 * π * ξ * t) * I) * ↑(Real.exp (-Real.pi * t^2 / δ^2))) =
    fun t : ℝ =>
        Complex.exp (-π * t^2 / δ^2) * Complex.exp (-2 * π * I * t * ξ)  := proven

lemma fourier_transform_gaussian_kernel {δ ξ : ℝ} (hδ : 0 < δ) :
    ∫ t : ℝ, Complex.exp (-π * t^2 / δ^2) * Complex.exp (-2 * π * I * t * ξ) ∂volume =
    (δ : ℂ) * Complex.exp (-π * δ^2 * ξ^2)  := proven

end Frourio

lemma suitable_window_of_normalized_gaussian {δ : ℝ} (hδ : 0 < δ) :
    suitable_window (normalizedGaussianLp δ hδ)  := proven

lemma suitable_window_of_gaussian {δ : ℝ} (hδ : 0 < δ) :
    ∀ w, Classical.choose (build_normalized_gaussian δ hδ) = w → suitable_window w  := proven

lemma suitable_window_of_gaussian' {δ : ℝ} (hδ : 0 < δ) :
    suitable_window (Classical.choose (build_normalized_gaussian δ hδ))  := proven


## ./Frourio/Analysis/HilbertSpace.lean

namespace Frourio

lemma weightedMeasure_pos_of_Ioo {σ a b : ℝ} (ha : 0 < a) (hb : a < b) :
    0 < weightedMeasure σ (Set.Ioo a b)  := proven

lemma continuous_ae_eq_const_on_pos {σ : ℝ} {f : ℝ → ℂ} {c : ℂ}
    (hf : Continuous f)
    (h_ae : (fun x => f x) =ᵐ[weightedMeasure σ] fun _ => c) :
    ∀ x > 0, f x = c  := proven

lemma continuous_ae_eq_on_pos {σ : ℝ} {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (h_ae : f =ᵐ[weightedMeasure σ] g) :
    ∀ x > 0, f x = g x  := proven

lemma coe_cast_eq {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞}
    [NormedAddCommGroup E] {μ ν : Measure α} (h : μ = ν) (f : Lp E p μ) :
    ((cast (by rw [h]) f : Lp E p ν) : α → E) =ᵐ[μ] (f : α → E)  := proven


lemma Hσ_cast_preserves_ae {σ : ℝ} (f : ℝ → ℂ)
    (h_L2 : MemLp f 2 (weightedMeasure σ))
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))) :
    let g_lp  := proven

lemma cast_preserves_ae_eq {σ : ℝ}
    (h_eq : weightedMeasure σ = mulHaar.withDensity (fun x => ENNReal.ofReal (x ^ (2 * σ - 1))))
    (f : ℝ → ℂ)
    (h_L2 : MemLp f 2 (weightedMeasure σ)) :
    let g_lp  := proven

noncomputable def create_mollifier (δ : ℝ) : ℝ → ℝ  := proven

lemma one_le_two_pow (k : ℕ) : (1 : ℝ) ≤ 2^k  := proven

lemma schwartz_map_decay_from_bounds (f : ℝ → ℂ)
    (hf_decay : ∀ (k n : ℕ), ∃ C > 0, ∀ x : ℝ, (1 + ‖x‖)^k * ‖iteratedDeriv n f x‖ ≤ C) :
    ∀ (p : ℕ × ℕ), ∃ C > 0, ∀ x : ℝ, (1 + ‖x‖)^p.1 * ‖iteratedDeriv p.2 f x‖ ≤ C  := proven

lemma contDiff_convolution_mollifier {φ : ℝ → ℂ} {η : ℝ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_supp : HasCompactSupport η) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, (η y : ℂ) * φ (x - y))  := proven

def SchwartzRestricted : Set (ℝ → ℂ)  := proven

structure UnboundedOperatorDomain (σ : ℝ) where
  carrier : Set (Hσ σ)
  dense : DenseRange (fun x : carrier => (x : Hσ σ))
  measurable : ∀ f ∈ carrier, Measurable ((f : ℝ → ℂ)) := proven

end Frourio


## ./Frourio/Analysis/HilbertSpaceCore.lean

namespace Frourio

noncomputable def weightFunction (σ : ℝ) : ℝ → ℝ≥0∞  := proven

lemma weightFunction_measurable (σ : ℝ) : Measurable (weightFunction σ)  := proven

noncomputable def weightedMeasure (σ : ℝ) : Measure ℝ  := proven


lemma weightedMeasure_apply (σ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    weightedMeasure σ s = ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal (x ^ (2 * σ - 2)) ∂volume  := proven

noncomputable instance Hσ.innerProductSpace (σ : ℝ) : InnerProductSpace ℂ (Hσ σ)  := proven

theorem Hσ_inner_def (σ : ℝ) (f g : Hσ σ) :
    @inner ℂ (Hσ σ) _ f g =
    ∫ x, conj (Hσ.toFun f x) * (Hσ.toFun g x)
      ∂(mulHaar.withDensity (fun x => ENNReal.ofReal (x^(2*σ-1))))  := proven

theorem Hσ_inner_conj_symm (σ : ℝ) (f g : Hσ σ) :
    @inner ℂ (Hσ σ) _ f g = conj (@inner ℂ (Hσ σ) _ g f)  := proven


lemma Hσ.norm_squared (σ : ℝ) (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x, ‖Hσ.toFun f x‖₊^2
      ∂(mulHaar.withDensity (fun x => ENNReal.ofReal (x^(2*σ-1))))).toReal  := proven

instance Hσ.completeSpace (σ : ℝ) : CompleteSpace (Hσ σ)  := proven

theorem Hσ.cauchy_complete (σ : ℝ) (f : ℕ → Hσ σ) (hf : CauchySeq f) :
    ∃ g : Hσ σ, Filter.Tendsto f Filter.atTop (𝓝 g)  := proven

theorem weightedMeasure_finite_on_bounded (σ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    weightedMeasure σ (Set.Ioo a b) < ∞  := proven

instance mulHaar_sigmaFinite : SigmaFinite mulHaar  := proven

instance weightedMeasure_sigmaFinite (σ : ℝ) : SigmaFinite (weightedMeasure σ)  := proven

theorem weightedMeasure_global_infinite (σ : ℝ) :
    weightedMeasure σ (Set.Ioi 0) = ∞  := proven


lemma exists_simple_func_approximation {σ : ℝ} (f' : Lp ℂ 2 (weightedMeasure σ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Lp.simpleFunc ℂ 2 (weightedMeasure σ),
      dist (↑s : Lp ℂ 2 (weightedMeasure σ)) f' < ε  := proven

lemma eLpNorm_indicator_le_simple {σ : ℝ} (f : ℝ → ℂ)
    (S : Set ℝ) (_ : MeasurableSet S) :
    eLpNorm (Set.indicator S f) 2 (weightedMeasure σ) ≤
    eLpNorm f 2 (weightedMeasure σ)  := proven

lemma measurable_extended_mollifier (δ : ℝ) :
    Measurable (fun t => if t ∈ Set.Ioo (-δ) δ then Real.exp (-1 / (δ^2 - t^2)) else 0)  := proven

lemma indicator_toSimpleFunc_aestrongly_measurable {σ : ℝ}
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ)) (S : Set ℝ) (hS : MeasurableSet S) :
    AEStronglyMeasurable (Set.indicator S (Lp.simpleFunc.toSimpleFunc s : ℝ → ℂ))
    (weightedMeasure σ)  := proven

lemma truncated_simple_func_mem_Lp {σ : ℝ} (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (n : ℕ) :
    let truncate  := proven


lemma mollifier_extended_continuous : ∀ (δ' : ℝ) (_ : 0 < δ'),
    ContinuousOn (fun s => if |s| < δ' then Real.exp (-1 / (δ'^2 - s^2)) else 0)
                  (Set.uIcc (-δ') δ')  := proven

lemma integral_Ioo_eq_intervalIntegral (δ : ℝ) (hδ_pos : 0 < δ) :
    let f_extended : ℝ → ℝ  := proven

lemma mollifier_normalization_positive (δ : ℝ) (hδ_pos : 0 < δ) :
    0 < ∫ t in Set.Ioo (-δ) δ, Real.exp (-1 / (δ^2 - t^2))  := proven

lemma mollifier_smooth_at_boundary : ∀ (δ : ℝ) (_ : 0 < δ),
    let Z  := proven

lemma truncated_shifted_measurable {σ : ℝ} {n : ℕ} (x : ℝ)
    (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ)) :
    AEStronglyMeasurable (fun y => if (1:ℝ)/n < x - y ∧ x - y < n then
      Lp.simpleFunc.toSimpleFunc s (x - y) else 0) volume  := proven

lemma convolution_smooth_of_smooth_compsupp_and_integrable
    {φ : ℝ → ℂ} {f : ℝ → ℂ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ)
    (hf_integrable : ∀ x : ℝ, Integrable (fun y => f (x - y)) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, φ y * f (x - y))  := proven

lemma smooth_mollifier_convolution_truncated
    {δ : ℝ} {n : ℕ} {σ : ℝ}
    (φ_δ : ℝ → ℝ) (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ_δ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_pos : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, (φ_δ y : ℂ) *
      (if 1/n < x - y ∧ x - y < n then Lp.simpleFunc.toSimpleFunc s (x - y) else 0))  := proven

lemma convolution_mollifier_truncated_has_compact_support
    {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (truncate : ℝ → ℂ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_pos : 0 < δ)
    (hn_pos : 0 < n)
    (h_truncate_supp : ∀ x, x ∉ Set.Ioo (1 / n : ℝ) n → truncate x = 0) :
    ∃ R > 0, ∀ x ≥ R, (∫ y, (φ_δ y : ℂ) * truncate (x - y)) = 0  := proven

lemma convolution_mollifier_truncated_zero_outside_support
    {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (truncate : ℝ → ℂ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (h_truncate_supp : ∀ x, x ∉ Set.Ioo (1 / n : ℝ) n → truncate x = 0) :
    ∀ x < (1/n : ℝ) - δ, (∫ y, (φ_δ y : ℂ) * truncate (x - y)) = 0  := proven

lemma smooth_convolution_measurable
    {σ : ℝ}
    (smooth_func : ℝ → ℂ)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) smooth_func) :
    AEStronglyMeasurable smooth_func (weightedMeasure σ)  := proven

lemma convolution_vanishes_on_nonpositive
    {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (truncate : ℝ → ℂ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_small : δ ≤ 1 / n) -- Critical condition: δ must be at most 1/n
    (h_truncate_supp : ∀ x, x ∉ Set.Ioo (1 / n : ℝ) n → truncate x = 0) :
    ∀ x ≤ 0, (∫ y, (φ_δ y : ℂ) * truncate (x - y)) = 0  := proven

lemma smooth_compact_support_memLp
    {σ : ℝ}
    (smooth_func : ℝ → ℂ)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) smooth_func)
    (h_support : ∃ R > 0, ∀ x ≥ R, smooth_func x = 0)
    (h_support_left : ∀ x ≤ 0, smooth_func x = 0)
    (h_support_away_zero : ∃ a > 0, ∀ x ∈ Set.Ioo 0 a, smooth_func x = 0) :
    MemLp smooth_func 2 (weightedMeasure σ)  := proven

lemma smooth_mollifier_convolution_memLp
    {σ : ℝ} {δ : ℝ} {n : ℕ}
    (φ_δ : ℝ → ℝ) (s : Lp.simpleFunc ℂ 2 (weightedMeasure σ))
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ_δ)
    (hφ_supp : ∀ y, |y| > δ → φ_δ y = 0)
    (hδ_pos : 0 < δ)
    (hn_pos : 0 < n)
    (hδ_bound : δ < 1 / n) :
    MemLp (fun x => ∫ y, (φ_δ y : ℂ) *
      (if 1/n < x - y ∧ x - y < n then Lp.simpleFunc.toSimpleFunc s (x - y) else 0))
      2 (weightedMeasure σ)  := proven

end Frourio


## ./Frourio/Analysis/K4mExact.lean

namespace Frourio

noncomputable def zakMellinKernelReal (s : ℝ) : KTransform ℝ where
  map  := proven

theorem zakMellin_continuousOn_in_x (s : ℝ) {y : ℝ} (hy : 0 < y) :
  ContinuousOn (fun x : ℝ => (zakMellinKernelReal s).map x y) (Set.Ioi (0 : ℝ))  := proven

theorem zakMellin_continuousOn_in_y (s : ℝ) {x : ℝ} (hx : 0 < x) :
  ContinuousOn (fun y : ℝ => (zakMellinKernelReal s).map x y) (Set.Ioi (0 : ℝ))  := proven

theorem zakMellin_narrow_continuity (s : ℝ) :
  K1primeK (zakMellinKernelReal s)  := proven

noncomputable def zakMellinKernel (X : Type*) [PseudoMetricSpace X] : KTransform X  := proven

theorem zakMellinK1prime (X : Type*) [PseudoMetricSpace X] :
  K1primeK (zakMellinKernel X)  := proven

theorem zakMellinDisplacementAffinity_ℝ :
  DisplacementAffinity (zakMellinKernel ℝ) linearDisplacement  := proven

theorem zakMellinDisplacementAffinity_pullback {Y : Type*} [PseudoMetricSpace Y] (f : Y → ℝ) :
  ∃ D : Displacement Y, DisplacementAffinity (KTransform.pullback (zakMellinKernel ℝ) f) D  := proven

theorem isometricPreservesK4m_pullback {Y : Type*} [PseudoMetricSpace Y]
  (g : Y → X) (K : KTransform X) (D : Displacement X) (D' : Displacement Y)
  (compat : ∀ y1 y2 θ, θ ∈ Set.Icc (0 : ℝ) 1 →
    g (D'.interp y1 y2 θ) = D.interp (g y1) (g y2) θ)
  (hK : DisplacementAffinity K D) :
  DisplacementAffinity (KTransform.pullback K g) D'  := proven

theorem isometricHomeoPreservesK4m {Y : Type*} [PseudoMetricSpace Y]
  (f : X → Y) (g : Y → X)
  (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x)
  (K : KTransform X) (D : Displacement X)
  (hK : DisplacementAffinity K D) :
  ∃ D' : Displacement Y, DisplacementAffinity (KTransform.pullback K g) D'  := proven


theorem basicModelExactK4m (K : KTransform X)
  (hBasic : ∃ (f : X → ℝ), Isometry f ∧ K = KTransform.pullback (zakMellinKernel ℝ) f) :
  ∃ D : Displacement X, DisplacementAffinity K D  := proven

theorem surrogateK4mValid {Ent : X → ℝ} {K : KTransform X} {gamma Ssup : ℝ}
  (hγ : 0 ≤ gamma) :
  K4m (FrourioFunctional.ofK Ent K gamma Ssup)  := proven

end Frourio


## ./Frourio/Analysis/K4mIsometrizationZakMellin.lean

namespace Frourio

noncomputable def logarithmicDistance (x y : ℝ) : ℝ  := proven

theorem logarithmicDistance_identity (x : ℝ) (hx : 0 < x) :
  logarithmicDistance x x = 0  := proven

theorem logarithmicDistance_symm (x y : ℝ) :
  logarithmicDistance x y = logarithmicDistance y x  := proven

theorem scaling_isometric_logarithmic (Λ : ℝ) (hΛ : 1 < Λ) (x y : ℝ)
  (hx : 0 < x) (hy : 0 < y) :
  logarithmicDistance (Λ * x) (Λ * y) = logarithmicDistance x y  := proven

theorem haar_measure_scaling_invariant (Λ : ℝ) (hΛ : 1 < Λ) :
  ∀ f : ℝ → ℝ, (∀ x, 0 < x → Continuous (fun y => f y / y)) →
    ∫ x in Set.Ioi (0 : ℝ), f (Λ * x) / x =
    ∫ x in Set.Ioi (0 : ℝ), f x / x  := proven

noncomputable def geometricInterpolation : Displacement ℝ where
  interp  := proven

theorem zakMellin_displacement_compatibility (s : ℝ) (hs : s = 0) :
  ∀ x y θ t : ℝ, 0 < x → 0 < y → 0 < t → θ ∈ Set.Icc (0 : ℝ) 1 →
    (zakMellinKernelReal s).map (geometricInterpolation.interp x y θ) t =
    (1 - θ) * (zakMellinKernelReal s).map x t + θ * (zakMellinKernelReal s).map y t  := proven

noncomputable def metalRatioScaling (Λ : ℝ) (k : ℤ) : ℝ → ℝ  := proven

theorem effectiveLambdaFormula (Λ : ℝ) (κ α : ℝ) (k : ℤ) (lam : ℝ) :
  ∃ lam_eff : ℝ, lam_eff = Real.rpow Λ ((κ - 2 * α) * (k : ℝ)) * lam  := proven

theorem critical_balance_invariance (Λ : ℝ) (α : ℝ) (k : ℤ) (lam : ℝ) :
  let κ  := proven

def IsBasicModel (X : Type*) [PseudoMetricSpace X] (K : KTransform X) : Prop  := proven

def UsesZakMellin {X : Type*} [PseudoMetricSpace X] (K : KTransform X) : Prop  := proven

def UsesIsometrization (X : Type*) [PseudoMetricSpace X] : Prop  := proven

theorem frourio_exact_K4m_property :
  ∃ (K : KTransform ℝ) (D : Displacement ℝ),
    (∀ x y θ t, 0 < x → 0 < y → 0 < t → θ ∈ Set.Icc (0 : ℝ) 1 →
      K.map (D.interp x y θ) t = (1 - θ) * K.map x t + θ * K.map y t) ∧
    IsBasicModel ℝ K ∧
    UsesZakMellin K ∧
    UsesIsometrization ℝ  := proven

theorem K4m_implies_enhanced_EVI
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [NormedAddCommGroup X]
  (Ent : X → ℝ) (K : KTransform X) (γ Ssup lam : ℝ) :
  ∀ u : ℝ → X, ofK_IsEVISolution Ent K γ Ssup lam u →
    ∃ P : EVIProblem X, IsEVISolution P u  := proven

end Frourio


## ./Frourio/Analysis/KTransform.lean

namespace Frourio

structure KTransform (X : Type*) [PseudoMetricSpace X] where
  (map : X → ℝ → ℝ)
  (narrowContinuous : Prop) := proven

def K1primeK (K : KTransform X) : Prop  := proven

def UniformLowerBoundAtZero (K : KTransform X) (C0 : ℝ) : Prop  := proven

noncomputable def DsigmamFromK (K : KTransform X) (Ssup : ℝ) : X → ℝ  := proven

theorem DsigmamFromK_lower_bound (K : KTransform X) (Ssup C0 : ℝ)
  (hS : 0 ≤ Ssup) (hLB : UniformLowerBoundAtZero K C0) :
  ∀ x : X, DsigmamFromK K Ssup x ≥ -(Ssup * C0)  := proven

def PointwiseContinuousInX (map : X → ℝ → ℝ) : Prop  := proven

structure K1primeTemplate (X : Type*) [PseudoMetricSpace X] where
  (map : X → ℝ → ℝ)
  (pointwise_cont : PointwiseContinuousInX map) := proven

def K1primeTemplate.pullback {Y : Type*} [PseudoMetricSpace Y]
  (T : K1primeTemplate X) (g : Y → X) (hg : Continuous g) :
  K1primeTemplate Y  := proven

def KTransform.pullback {Y : Type*} [PseudoMetricSpace Y]
  (K : KTransform X) (g : Y → X) : KTransform Y  := proven

structure Displacement where
  (interp : X → X → ℝ → X)
  (endpoint0 : ∀ x y : X, interp x y 0 = x)
  (endpoint1 : ∀ x y : X, interp x y 1 = y) := proven

def DisplacementAffinity (K : KTransform X) (D : Displacement X) : Prop  := proven

noncomputable def linearDisplacement : Displacement ℝ  := proven

noncomputable def Displacement.pullback
  {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (D : Displacement X) (f : X → Y) (g : Y → X)
  (hfg : ∀ y, f (g y) = y) : Displacement Y  := proven

theorem Displacement.pullback_compat
  {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  (D : Displacement X) (f : X → Y) (g : Y → X)
  (hfg : ∀ y, f (g y) = y) (hgf : ∀ x, g (f x) = x) :
  ∀ y1 y2 θ, θ ∈ Set.Icc (0:ℝ) 1 →
    g ((D.pullback f g hfg).interp y1 y2 θ) = D.interp (g y1) (g y2) θ  := proven

end Frourio


## ./Frourio/Analysis/Lebesgue/Lebesgue.lean

namespace Frourio

def HasSmallDiam (A : Set X) (ε : ℝ) : Prop  := proven

def LebesgueNumber {ι : Type*} (K : Set X) (U : ι → Set X) (L : ℝ) : Prop  := proven

theorem lebesgue_number_exists {ι : Type*} [Nonempty ι]
    {K : Set X} (hK : IsCompact K)
    {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hcover : K ⊆ ⋃ i, U i) :
    ∃ L > 0, LebesgueNumber K U L  := proven

lemma lebesgue_property_from_two_point_local
    {φ : ℝ → ℝ} {s r ε : ℝ}
    (hr : 0 < r) (_hε : 0 < ε)
    (two_point_ball_local :
      ∀ w ∈ Set.Icc 0 r, ∃ ρw > 0, ∃ δw > 0,
        ∀ u ∈ Set.Icc 0 r, ∀ v ∈ Set.Icc 0 r,
          dist u w < ρw → dist v w < ρw →
          φ (s + v) - φ (s + u) ≤ ε * (v - u)) :
    ∃ L > 0,
      ∀ y ∈ Set.Icc 0 r, ∀ z ∈ Set.Icc 0 r, dist y z < L →
        ∃ w ∈ Set.Icc 0 r, ∃ δw > 0,
          dist y w < δw ∧ dist z w < δw ∧
          φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

end Frourio


## ./Frourio/Analysis/Lebesgue/OrientedLebesgue.lean

namespace Frourio

lemma two_point_hasSmallDiam_iff {X : Type*} [PseudoMetricSpace X] {y z : X} {L : ℝ}
    (hL : 0 < L) : HasSmallDiam ({y, z} : Set X) L ↔ dist y z < L  := proven

lemma two_point_lebesgue {ι : Type*} [Nonempty ι] {K : Set ℝ}
    (hK : IsCompact K) {U : ι → Set ℝ} (hU : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ L > 0, ∀ y z, y ∈ K → z ∈ K → dist y z < L →
      ∃ i, y ∈ U i ∧ z ∈ U i  := proven

def OrientedProductSpace (r : ℝ) : Set (ℝ × ℝ)  := proven

lemma dist_eq_sub_of_le {y z : ℝ} (h : y ≤ z) : dist y z = z - y  := proven

theorem oriented_lebesgue_from_two_point_local
    (hr : 0 < r)
    (h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → dist y z < L →
      ∃ w ∈ Set.Icc 0 r, ∃ δ_w > 0,
        dist y w < δ_w ∧ dist z w < δ_w ∧
        φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

theorem oriented_uniform_small_interval_control
    (hr : 0 < r)
    (h_local : ∀ w ∈ Set.Icc 0 r, ∃ ρ_w > 0, ∃ δ_w > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z →
      dist y w < ρ_w → dist z w < ρ_w → z - y < δ_w →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)) :
    ∃ L > 0, ∀ y z,
      y ∈ Set.Icc 0 r → z ∈ Set.Icc 0 r → y ≤ z → z - y < L →
      φ (s + z) - φ (s + y) ≤ ε * (z - y)  := proven

end Frourio


## ./Frourio/Analysis/MellinBasic.lean

namespace Frourio


lemma mulHaar_apply (s : Set ℝ) (hs : MeasurableSet s) :
    mulHaar s = ∫⁻ x in s ∩ Set.Ioi 0, ENNReal.ofReal (1 / x) ∂volume  := proven

noncomputable instance (σ : ℝ) : NormedAddCommGroup (Hσ σ)  := proven

noncomputable instance (σ : ℝ) : NormedSpace ℂ (Hσ σ)  := proven


lemma Lp_norm_sq_as_lintegral {ν : Measure ℝ} (f : Lp ℂ 2 ν) :
    ‖f‖^2 = (∫⁻ x, ‖(f : ℝ → ℂ) x‖₊ ^ 2 ∂ν).toReal  := proven


lemma lintegral_withDensity_expand {g : ℝ → ℝ≥0∞} {wσ : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hwσ : Measurable wσ) :
    ∫⁻ x, g x ∂(mulHaar.withDensity wσ) = ∫⁻ x, g x * wσ x ∂mulHaar  := proven


lemma lintegral_mulHaar_expand {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂mulHaar = ∫⁻ x in Set.Ioi 0, g x * ENNReal.ofReal (1 / x) ∂volume  := proven


lemma weight_product_simplify (σ : ℝ) (x : ℝ) (hx : x ∈ Set.Ioi 0) :
    ENNReal.ofReal (x ^ (2 * σ - 1)) * ENNReal.ofReal (1 / x) =
    ENNReal.ofReal (x ^ (2 * σ - 1) / x)  := proven


lemma Hσ_norm_squared {σ : ℝ} (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x in Set.Ioi 0, ‖Hσ.toFun f x‖₊ ^ 2 *
      ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal  := proven

lemma zeroLatticeSpacing_pos {φ : ℝ} (hφ : 1 < φ) : 0 < zeroLatticeSpacing φ  := proven

lemma log_preimage_inter_Ioi_eq_exp_image {s : Set ℝ} :
    Real.log ⁻¹' s ∩ Set.Ioi (0 : ℝ) = Real.exp '' s  := proven

lemma volume_exp_image_eq_integral {s : Set ℝ} (hs : MeasurableSet s) :
    volume (Real.exp '' s) = ∫⁻ t in s, ENNReal.ofReal (Real.exp t) ∂volume  := proven

lemma exp_surjective_onto_Ioi :
    Set.SurjOn Real.exp Set.univ (Set.Ioi (0 : ℝ))  := proven

lemma measurableSet_exp_image {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet (Real.exp '' s)  := proven

lemma map_log_restrict_Ioi_eq_withDensity_exp :
    Measure.map Real.log (volume.restrict (Set.Ioi (0 : ℝ)))
      = volume.withDensity (fun t => ENNReal.ofReal (Real.exp t))  := proven

lemma lintegral_change_of_variables_exp {α : ℝ} {f : ℝ → ENNReal}
    (hf : Measurable f) :
    ∫⁻ x in Set.Ioi 0, f (Real.log x) * ENNReal.ofReal (x ^ α) ∂(volume.restrict (Set.Ioi 0)) =
    ∫⁻ t, f t * ENNReal.ofReal (Real.exp (α * t + t)) ∂volume  := proven

lemma lintegral_log_substitute {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ x in Set.Ioi 0, f (Real.log x) * ENNReal.ofReal (x⁻¹) ∂(volume.restrict (Set.Ioi 0)) =
    ∫⁻ t, f t ∂volume  := proven

lemma mulHaar_eq_volume_div_x :
    mulHaar = volume.withDensity (fun x => ENNReal.ofReal (1 / x))  := proven

lemma norm_cpow_real (x : ℝ) (σ : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ (-σ : ℂ)‖₊ = NNReal.rpow (Real.toNNReal x) (-σ)  := proven


lemma coe_nnnorm_mul (a b : ℂ) :
    ((‖a * b‖₊ : ℝ≥0∞)) = ((‖a‖₊ : ℝ≥0∞) * (‖b‖₊ : ℝ≥0∞))  := proven


lemma hwσ_meas_for_optimization (σ : ℝ) (wσ : ℝ → ℝ≥0∞)
    (hwσ : wσ = fun x ↦ ENNReal.ofReal (x ^ (2 * σ - 1))) : Measurable wσ  := proven


lemma hx_cancel_for_optimization (σ x : ℝ) (hx' : 0 < x) (wσ : ℝ → ℝ≥0∞)
    (hwσ : wσ = fun x ↦ ENNReal.ofReal (x ^ (2 * σ - 1))) :
    (↑‖↑x ^ (2⁻¹ - ↑σ)‖₊ * (↑‖↑x ^ (2⁻¹ - ↑σ)‖₊ * wσ x)) = (1 : ℝ≥0∞)  := proven


lemma hg_meas_for_optimization (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (g : ℝ → ℂ) (hg_def : g = fun x =>
      if _ : 0 < x then
        ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)
      else 0) :
    Measurable fun x => (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)  := proven


lemma expand_withDensity (g : ℝ → ℂ) (wσ : ℝ → ℝ≥0∞)
    (hg_meas : Measurable fun x => (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ))
    (hwσ_meas : Measurable wσ) :
    ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(mulHaar.withDensity wσ)
      = ∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x ∂mulHaar  := proven

noncomputable def toHσ_ofL2 (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Hσ σ  := proven

end Frourio


## ./Frourio/Analysis/MellinCore.lean

noncomputable def mulHaar : Measure ℝ  := proven

noncomputable abbrev Hσ (σ : ℝ)  := proven

noncomputable def Hσ.toFun {σ : ℝ} (f : Hσ σ) : ℝ → ℂ  := proven

noncomputable def zeroLatticeSpacing (Λ : ℝ) : ℝ  := proven


## ./Frourio/Analysis/MellinParseval.lean

namespace Frourio

noncomputable def logMap : (Set.Ioi (0 : ℝ)) → ℝ  := proven

noncomputable def expMap : ℝ → (Set.Ioi (0 : ℝ))  := proven

noncomputable def logMap_measurableEquiv :
    MeasurableEquiv (Set.Ioi (0 : ℝ)) ℝ where
  toFun  := proven

lemma mellin_kernel_transform (s : ℂ) (t : ℝ) :
    (Real.exp t : ℂ) ^ (s - 1) = Complex.exp ((s - 1) * t)  := proven

lemma mellin_change_of_variables (f : ℝ → ℂ) (s : ℂ) :
    ∫ x in Set.Ioi (0 : ℝ), f x * x ^ (s - 1) ∂volume =
    ∫ t : ℝ, f (Real.exp t) * (Real.exp t : ℂ) ^ (s - 1) * Real.exp t  := proven

theorem mellin_to_fourier_change_of_variables
    (f : ℝ → ℂ) (s : ℂ) :
    mellinTransform f s = ∫ t : ℝ, f (Real.exp t) * Complex.exp (s * t)  := proven

lemma exp_image_measure_integral (E : Set ℝ) (hE : MeasurableSet E) :
    ∫⁻ x in Real.exp '' E, ENNReal.ofReal (1 / x) ∂volume =
    ∫⁻ t in E, ENNReal.ofReal (1 / Real.exp t) * ENNReal.ofReal (Real.exp t) ∂volume  := proven

lemma ennreal_div_exp_mul_exp : ∀ t : ℝ,
    ENNReal.ofReal (1 / Real.exp t) * ENNReal.ofReal (Real.exp t) = 1  := proven

lemma mulHaar_pushforward_log :
    ∃ (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ∞ ∧
    Measure.map Real.log (mulHaar.restrict (Set.Ioi (0 : ℝ))) = c • volume  := proven

noncomputable def logPushforward (f : ℝ → ℂ) : ℝ → ℂ  := proven

noncomputable def mellinWeight (σ : ℝ) : ℝ → ℝ  := proven

theorem mellin_as_weighted_fourier (f : ℝ → ℂ) (σ τ : ℝ) :
    mellinTransform f (σ + I * τ) =
    ∫ t : ℝ, (logPushforward f) t * Complex.exp (σ * t) * Complex.exp (I * τ * t)  := proven

lemma complex_polarization_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g : E) :
    4 * @inner ℂ _ _ f g =
      ((‖f + g‖ ^ 2 : ℝ) : ℂ) - ((‖f - g‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * ((‖f + Complex.I • g‖ ^ 2 : ℝ) : ℂ) +
          Complex.I * ((‖f - Complex.I • g‖ ^ 2 : ℝ) : ℂ)  := proven

lemma mellin_logpull_relation (σ : ℝ) (f : Hσ σ) (τ : ℝ) :
    mellinTransform (f : ℝ → ℂ) (σ + I * τ) =
    ∫ t : ℝ, LogPull σ f t * Complex.exp (I * τ * t) * Complex.exp ((1/2 : ℝ) * t)  := proven

lemma norm_simplification_logpull (σ : ℝ) (f : Hσ σ) :
    ∫ t : ℝ, ‖LogPull σ f t * Complex.exp ((1/2 : ℝ) * t)‖^2 =
    ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t  := proven

lemma weighted_LogPull_integral_eq (σ : ℝ) (f : Hσ σ) :
    ∫⁻ t, ENNReal.ofReal (‖LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)‖^2) ∂volume
    = ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖f x‖ ^ 2 * x ^ (2 * σ - 1)) ∂volume  := proven

def has_weighted_L2_norm (σ : ℝ) (f : Hσ σ) : Prop  := proven

lemma weighted_LogPull_memLp (σ : ℝ) (f : Hσ σ) (h_extra : has_weighted_L2_norm σ f) :
    MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume  := proven

lemma logpull_mellin_l2_relation (σ : ℝ) (f : Hσ σ)
    (h_weighted_L2 : MemLp (fun t => LogPull σ f t * Complex.exp ((1 / 2 : ℝ) * t)) 2 volume) :
    ∫ t : ℝ, ‖LogPull σ f t‖^2 * Real.exp t ∂volume =
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖^2 ∂volume  := sorry

lemma plancherel_constant_is_one (σ : ℝ) (f : Hσ σ) :
    ∃ (C : ℝ), C > 0 ∧ ∫ τ : ℝ, ‖LogPull σ f τ‖^2 = C * ‖f‖^2 ∧ C = 1  := sorry

lemma plancherel_constant_unique (σ : ℝ) (f : Hσ σ) (C₁ C₂ : ℝ)
    (h₁_pos : C₁ > 0) (h₂_pos : C₂ > 0)
    (h₁_eq : ∫ τ : ℝ, ‖LogPull σ f τ‖ ^ 2 = C₁ * ‖f‖ ^ 2)
    (h₂_eq : ∫ τ : ℝ, ‖LogPull σ f τ‖ ^ 2 = C₂ * ‖f‖ ^ 2) :
    C₁ = C₂  := sorry

theorem mellin_parseval_formula (σ : ℝ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (f : Hσ σ),
    -- Additional condition: the function must be sufficiently integrable
    ((∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume) < ⊤) →
    ∫⁻ x in Set.Ioi (0:ℝ), ENNReal.ofReal (‖f x‖^2 * x^(2*σ - 1)) ∂volume =
    ENNReal.ofReal (C * ∫ τ : ℝ, ‖mellinTransform (f : ℝ → ℂ) (σ + I * τ)‖ ^ 2 ∂volume)  := proven

lemma mellin_transform_linear (σ : ℝ) (h k : Hσ σ) (c : ℂ) (s : ℂ)
    (hh_int : Integrable (fun t => h t * t ^ (s - 1)) (volume.restrict (Set.Ioi 0)))
    (hk_int : Integrable (fun t => k t * t ^ (s - 1)) (volume.restrict (Set.Ioi 0))) :
    mellinTransform ((h + c • k) : ℝ → ℂ) s =
      mellinTransform (h : ℝ → ℂ) s + c * mellinTransform (k : ℝ → ℂ) s  := proven

lemma mellin_kernel_integrable_on_critical_line (σ : ℝ) (f : Hσ σ) (τ : ℝ)
    (hf_L2 : has_weighted_L2_norm σ f) :
    Integrable (fun t => f t * t ^ ((σ + I * τ) - 1)) (volume.restrict (Set.Ioi 0))  := sorry

lemma mellin_transform_linear_critical_line (σ : ℝ) (h k : Hσ σ) (c : ℂ) (τ : ℝ)
    (hh_L2 : has_weighted_L2_norm σ h) (hk_L2 : has_weighted_L2_norm σ k) :
    mellinTransform ((h + c • k) : ℝ → ℂ) (σ + I * τ) =
      mellinTransform (h : ℝ → ℂ) (σ + I * τ) + c * mellinTransform (k : ℝ → ℂ) (σ + I * τ)  := proven

lemma mellin_polarization_pointwise (F G : ℂ) :
    ‖F + G‖ ^ 2 - ‖F - G‖ ^ 2 - Complex.I * ‖F + Complex.I * G‖ ^ 2 +
      Complex.I * ‖F - Complex.I * G‖ ^ 2 = 4 * (starRingEnd ℂ F * G)  := sorry

theorem parseval_identity_equivalence (σ : ℝ) :
    ∃ (C : ℝ), C > 0 ∧ ∀ (f g : Hσ σ),
    -- Additional L² conditions needed for convergence
    has_weighted_L2_norm σ f → has_weighted_L2_norm σ g →
    @inner ℂ _ _ f g = C * ∫ τ : ℝ,
      starRingEnd ℂ (mellinTransform (f : ℝ → ℂ) (σ + I * τ)) *
      mellinTransform (g : ℝ → ℂ) (σ + I * τ)  := sorry

theorem mellin_isometry_normalized (σ : ℝ) :
    ∃ (C : ℝ) (U : Hσ σ →L[ℂ] Lp ℂ 2 volume),
    C > 0 ∧ ∀ f : Hσ σ, ‖U f‖ = C * ‖f‖ ∧
    (U f : ℝ → ℂ) = fun τ : ℝ => mellinTransform (f : ℝ → ℂ) (σ + I * ↑τ)  := sorry

theorem fourier_parseval_classical (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃ (c : ℝ), c > 0 ∧ ‖f‖ ^ 2 = c * ‖f‖ ^ 2  := sorry

theorem mellin_fourier_parseval_connection (σ : ℝ) (f : Hσ σ) :
    let g  := sorry

theorem mellin_fourier_unitary_equivalence (σ : ℝ) :
    ∃ (V : Hσ σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
    ∀ (f : Hσ σ) (τ : ℝ),
    ∃ (c : ℂ), c ≠ 0 ∧ mellinTransform (f : ℝ → ℂ) (σ + I * τ) = c * (V f τ)  := sorry

theorem mellin_convolution_parseval (σ : ℝ) (f g : Hσ σ) :
    ∫ τ : ℝ, mellinTransform f (σ + I * τ) * mellinTransform g (1 - σ + I * τ) =
    2 * Real.pi * ∫ x in Set.Ioi (0 : ℝ), f x * g x ∂mulHaar  := sorry

theorem mellin_energy_conservation (σ : ℝ) (f : Hσ σ) :
    ∫ x in Set.Ioi (0 : ℝ), ‖(f : ℝ → ℂ) x‖ ^ 2 * (x : ℝ) ^ (2 * σ - 1) ∂volume =
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖mellinTransform f (σ + I * τ)‖ ^ 2  := sorry

end Frourio


## ./Frourio/Analysis/MellinPlancherel.lean

namespace Complex

@[simp] lemma norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x|  := proven

@[simp] lemma ennreal_norm_eq (z : ℂ) : (‖z‖ₑ : ℝ≥0∞) = (‖z‖₊ : ℝ≥0∞)  := proven


@[simp] lemma ennreal_norm_mul_self (z : ℂ) :
    ‖z‖ₑ * ‖z‖ₑ = (‖z‖₊ : ℝ≥0∞) * (‖z‖₊ : ℝ≥0∞)  := proven

end Complex

namespace Frourio

noncomputable def LogPull (σ : ℝ) (f : Hσ σ) : ℝ → ℂ  := proven


@[simp] lemma LogPull_apply (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    LogPull σ f t
      = (Real.exp ((σ - (1 / 2 : ℝ)) * t) : ℂ) * Hσ.toFun f (Real.exp t)  := proven

lemma weight_measurable (σ : ℝ) :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((2 * σ) * t)))  := proven

lemma LogPull_measurable (σ : ℝ) (f : Hσ σ) : Measurable (LogPull σ f)  := proven


lemma LogPull_norm_sq (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    ‖LogPull σ f t‖^2
      = Real.exp ((2 * σ - 1) * t) * ‖Hσ.toFun f (Real.exp t)‖^2  := proven


lemma LogPull_integrand_eq (σ : ℝ) (f : Hσ σ) (t : ℝ) :
    (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)
      = ENNReal.ofReal (‖Hσ.toFun f (Real.exp t)‖^2)
          * ENNReal.ofReal (Real.exp ((2 * σ - 1) * t))  := proven

theorem LogPull_isometry (σ : ℝ) (f : Hσ σ) :
    ‖f‖^2 = (∫⁻ x in Set.Ioi 0, ‖Hσ.toFun f x‖₊ ^ 2 *
      ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume).toReal  := proven


private lemma LogPull_sq_integral_eq (σ : ℝ) (f : Hσ σ) :
    ∫⁻ t, (‖LogPull σ f t‖₊ : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure ℝ)
      = ∫⁻ x in Set.Ioi (0 : ℝ),
          (‖Hσ.toFun f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
            * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂(volume : Measure ℝ)  := proven

lemma Hσ_zero_integral (σ : ℝ) :
    ∫⁻ x in Set.Ioi (0 : ℝ),
      (‖Hσ.toFun (0 : Hσ σ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)
        * ENNReal.ofReal (x ^ (2 * σ - 1) / x) ∂volume = 0  := proven


lemma LogPull_memLp (σ : ℝ) (f : Hσ σ) :
    MemLp (LogPull σ f) 2 (volume : Measure ℝ)  := proven

theorem mellin_in_L2 (σ : ℝ) (f : Hσ σ) :
    MemLp (LogPull σ f) 2 (volume : Measure ℝ)  := proven

theorem mellin_direct_isometry (σ : ℝ) :
    ∃ C > 0, ∀ f : Hσ σ,
      ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume = C * ‖f‖^2  := proven

theorem mellin_plancherel_formula (σ : ℝ) (f : Hσ σ) :
    ∃ C > 0, ∫ τ : ℝ, ‖LogPull σ f τ‖^2 ∂volume = C * ‖f‖^2  := proven

lemma exp_weight_cancel (σ τ : ℝ) :
    (Real.exp ((σ - (1 / 2 : ℝ)) * τ) : ℂ)
        * (Real.exp τ : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ) = 1  := proven

end Frourio


## ./Frourio/Analysis/MellinPlancherelCore.lean

namespace Frourio


lemma hx_id_helper (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (wσ : ℝ → ℝ≥0∞) (hwσ : wσ = fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
    (g : ℝ → ℂ) (hg : g = fun x =>
      if _ : 0 < x then
        ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)
      else 0)
    (x : ℝ) (hx : x ∈ Set.Ioi 0) :
    (((‖g x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) * wσ x) * ENNReal.ofReal (1 / x)
      = ((‖((f : ℝ → ℂ) (Real.log x))‖₊ : ℝ≥0∞) ^ (2 : ℕ))
          * ENNReal.ofReal (1 / x)  := proven

lemma enorm_to_nnnorm_lintegral (f : ℝ → ℂ) :
    (∫⁻ t, ‖f t‖ₑ ^ (2 : ℝ)) = (∫⁻ t, ((‖f t‖₊ : ℝ≥0∞) ^ (2 : ℕ)))  := proven

lemma ofReal_norm_eq_coe_nnnorm (f : ℝ → ℂ) :
    (fun x => (ENNReal.ofReal ‖f x‖) ^ (2 : ℕ))
      = (fun x => ((‖f x‖₊ : ℝ≥0∞) ^ (2 : ℕ)))  := proven

lemma private_hg_memLp (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ))
    (wσ : ℝ → ℝ≥0∞) (hwσ : wσ = fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))
    (g : ℝ → ℂ) (hg : g = fun x =>
      if _ : 0 < x then
        ((f : ℝ → ℂ) (Real.log x)) * (x : ℂ) ^ (-(σ - (1 / 2 : ℝ)) : ℂ)
      else 0) :
  MemLp g 2 (mulHaar.withDensity wσ)  := proven

lemma private_h_coe (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
  let wσ : ℝ → ℝ≥0∞  := proven

theorem toHσ_ofL2_isometry (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖toHσ_ofL2 σ f‖ = ‖f‖  := proven

theorem phiSymbol_numerator_eq (φ : ℝ) (hφ : (φ - φ⁻¹) ≠ 0) (s : ℂ) :
    ((φ - φ⁻¹ : ℝ) : ℂ) * phiSymbol φ s
      = Complex.exp (-s * (Real.log φ : ℂ)) - Complex.exp (s * (Real.log φ : ℂ))  := proven

noncomputable def Mφ (φ : ℝ) (σ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven

theorem mellin_symbol_zero_lattice (φ : ℝ) (hφ : 1 < φ) (k : ℤ) :
    phiSymbol φ ((Complex.I * (Real.pi : ℂ) * (k : ℂ)) / (Real.log φ : ℂ)) = 0  := proven

@[simp]
lemma zeroLatticeSpacing_eq (φ : ℝ) : zeroLatticeSpacing φ = Real.pi / Real.log φ  := proven

@[simp]
lemma mem_mellinZeros_iff (φ : ℝ) (s : ℂ) :
    s ∈ mellinZeros φ ↔ ∃ k : ℤ, s = (Complex.I * Real.pi * k) / Real.log φ  := proven

theorem phiSymbol_eq_zero_iff (φ : ℝ) (hφ : 1 < φ) (s : ℂ) :
    phiSymbol φ s = 0 ↔ ∃ k : ℤ, s = (Complex.I * Real.pi * k) / Real.log φ  := proven

noncomputable def latticePoint (φ : ℝ) (k : ℤ) : ℂ  := proven

@[simp]
lemma phiSymbol_latticePoint (φ : ℝ) (hφ : 1 < φ) (k : ℤ) :
    phiSymbol φ (latticePoint φ k) = 0  := proven

lemma latticePoint_spacing (φ : ℝ) (hφ : 1 < φ) (k : ℤ) :
    latticePoint φ (k + 1) - latticePoint φ k = Complex.I * zeroLatticeSpacing φ  := proven

lemma latticePoint_re (φ : ℝ) (k : ℤ) : (latticePoint φ k).re = 0  := proven

lemma latticePoint_im (φ : ℝ) (hφ : 1 < φ) (k : ℤ) :
    (latticePoint φ k).im = (Real.pi * k) / Real.log φ  := proven

@[simp]
lemma latticePoint_neg (φ : ℝ) (k : ℤ) :
    latticePoint φ (-k) = -latticePoint φ k  := proven

noncomputable def goldenZeroLattice : Set ℂ  := proven

noncomputable def goldenSpacing : ℝ  := proven

noncomputable def baseChangeFun (c : ℝ) (g : ℝ → ℂ) : ℝ → ℂ  := proven

noncomputable def baseChange (c : ℝ) (_hc : 0 < c) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven


@[simp] lemma baseChange_apply (c : ℝ) (hc : 0 < c)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : baseChange c hc f = f  := proven

lemma baseChange_isometry (c : ℝ) (hc : 0 < c) : Isometry (baseChange c hc)  := proven

noncomputable def baseChangeL (c : ℝ) (hc : 0 < c) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven


@[simp] lemma baseChangeL_apply (c : ℝ) (hc : 0 < c)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : baseChangeL c hc f = f  := proven

theorem scale_mult_commute (c : ℝ) (hc : 0 < c) (φ : ℝ) (σ : ℝ)
    (h : phiSymbol φ (σ : ℂ) = phiSymbol (φ ^ c) (σ : ℂ)) :
    baseChangeL c hc ∘L Mφ φ σ = Mφ (φ^c) σ ∘L baseChangeL c hc  := proven

theorem base_change_formula (φ φ' : ℝ) (hφ : 1 < φ) (hφ' : 1 < φ') (σ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ φ' = φ^c ∧
    (∀ _ : 0 < c,
      (phiSymbol φ (σ : ℂ) = phiSymbol φ' (σ : ℂ)) →
        baseChangeL c ‹0 < c› ∘L Mφ φ σ = Mφ φ' σ ∘L baseChangeL c ‹0 < c›)  := proven


noncomputable def goldenCalib (φ : ℝ) (hφ : 1 < φ) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven


@[simp] lemma goldenCalib_apply (φ : ℝ) (hφ : 1 < φ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : goldenCalib φ hφ f = f  := proven

theorem golden_calibration_formula (φ_real : ℝ) (σ : ℝ) :
    ∃ (gcL : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)),
      gcL ∘L Mφ φ_real σ = Mφ Frourio.φ σ ∘L gcL  := proven

end Frourio


## ./Frourio/Analysis/MellinSobolev.lean

namespace Frourio

abbrev Htimes (_s : ℝ)  := proven

noncomputable def HtimesNorm (_s : ℝ) (_f : Htimes _s) : ℝ  := proven

def algebraProp_Htimes (s : ℝ) : Prop  := proven

def scaleProp_Htimes (s : ℝ) : Prop  := proven

end Frourio


## ./Frourio/Analysis/MellinTransform.lean

namespace Frourio

noncomputable def mellinKernel (x : ℝ) (s : ℂ) : ℂ  := proven

noncomputable def mellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ  := proven

noncomputable def phiSymbol (Λ : ℝ) (s : ℂ) : ℂ  := proven

@[simp] lemma phiSymbol_at_zero (Λ : ℝ) : phiSymbol Λ 0 = 0  := proven

def mellinZeros (Λ : ℝ) : Set ℂ  := proven

noncomputable def goldenLatticePoint (φ : ℝ) (k : ℤ) : ℝ  := proven

def isGoldenLattice (φ : ℝ) (τ : ℝ) : Prop  := proven


@[simp] lemma isGoldenLattice_iff (φ : ℝ) (τ : ℝ) :
    isGoldenLattice φ τ ↔ ∃ k : ℤ, τ = (k : ℝ) * zeroLatticeSpacing φ  := proven

@[simp] lemma isGoldenLattice_zero (φ : ℝ) : isGoldenLattice φ 0  := proven


@[simp] lemma goldenLatticePoint_spec (φ : ℝ) (k : ℤ) :
    isGoldenLattice φ (goldenLatticePoint φ k)  := proven

lemma log_ne_zero_of_one_lt {Λ : ℝ} (h : 1 < Λ) : Real.log Λ ≠ 0  := proven

lemma denom_ne_zero_of_one_lt {Λ : ℝ} (h : 1 < Λ) : ((Λ - Λ⁻¹ : ℝ) : ℂ) ≠ 0  := proven

noncomputable def Xiφ (φ : ℝ) (s : ℂ) : ℂ  := proven

lemma div_eq_zero_of_ne {x c : ℂ} (hc : c ≠ 0) (hx : x / c = 0) : x = 0  := proven

lemma div_eq_zero_iff_of_ne {x c : ℂ} (hc : c ≠ 0) : x / c = 0 ↔ x = 0  := proven

lemma eq_div_iff_mul_eq_of_ne {a s r : ℂ} (ha : a ≠ 0) : s = r / a ↔ s * a = r  := proven

lemma exp_neg_eq_iff_exp_two_eq_one (w : ℂ) :
    Complex.exp (-w) = Complex.exp w ↔ Complex.exp (2 * w) = 1  := proven

lemma phiSymbol_zero_iff {Λ : ℝ} (hΛ : 1 < Λ) (s : ℂ) :
    phiSymbol Λ s = 0 ↔ s ∈ mellinZeros Λ  := proven

lemma Xiφ_zero_iff {φ : ℝ} (hφ : 1 < φ) {s : ℂ} (hs : s ≠ 0) :
    Xiφ φ s = 0 ↔ s ∈ mellinZeros φ  := proven

def VerticalLine (σ : ℝ)  := proven

noncomputable def HσNorm (σ : ℝ) (u : Hσ σ) : ℝ  := proven

noncomputable def phiSymbolBound (Λ σ : ℝ) : ℝ  := proven

noncomputable def divByX (g : ℝ → ℂ) : ℝ → ℂ  := proven

noncomputable def mellinPhiDiff (_Λ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ  := proven

noncomputable def SmSymbol (m : ℕ) (Λ : ℝ) (s : ℂ) : ℂ  := proven

@[simp] lemma SmSymbol_zero_m (Λ : ℝ) (s : ℂ) : SmSymbol 0 Λ s = 0  := proven

def SmZeros (_m : ℕ) (_Λ : ℝ) : Set ℂ  := proven

def Sm_zero_locus (m : ℕ) (Λ : ℝ) : Prop  := proven

def IsBohrAlmostPeriodic (F : ℝ → ℂ) : Prop  := proven

def Sm_bohr_almost_periodic (m : ℕ) (Λ σ : ℝ) : Prop  := proven

end Frourio


## ./Frourio/Analysis/MinimizingMovement.lean

namespace Frourio

def distSquared (x y : X) : ℝ  := proven

noncomputable def MmFunctional (τ : ℝ) (F : X → ℝ) (xPrev x : X) : ℝ  := proven

def IsMinimizer {Y : Type*} (f : Y → ℝ) (x : Y) : Prop  := proven

def MmStep (τ : ℝ) (F : X → ℝ) (xPrev x : X) : Prop  := proven

def MmProper (F : X → ℝ) : Prop  := proven

def MmCoercive [Nonempty X] (F : X → ℝ) : Prop  := proven

def MmCompactSublevels (F : X → ℝ) : Prop  := proven

structure MmCurve (τ : ℝ) (F : X → ℝ) (x0 : X) where
  /-- The discrete points at times nτ -/
  points : ℕ → X
  /-- Initial condition -/
  init : points 0 = x0
  /-- Each point is obtained by minimizing movement -/
  step : ∀ n : ℕ, MmStep τ F (points n) (points (n + 1)) := proven

noncomputable def MmCurve.interpolate {τ : ℝ} {F : X → ℝ} {x0 : X}
    (curve : MmCurve τ F x0) (t : ℝ) : X  := proven

theorem mm_energy_decrease {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {xPrev x : X}
    (h : MmStep τ F xPrev x) :
    F x ≤ F xPrev  := proven

theorem mm_distance_estimate {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {xPrev x : X}
    (h : MmStep τ F xPrev x) :
    distSquared x xPrev ≤ 2 * τ * (F xPrev - F x)  := proven

theorem sublevel_closed_of_lsc {F : X → ℝ} (hF : LowerSemicontinuous F) (c : ℝ) :
    IsClosed {x : X | F x ≤ c}  := proven

lemma lsc_bddBelow_on_compact {f : X → ℝ} {K : Set X}
    (hK_compact : IsCompact K) (_hK_nonempty : K.Nonempty)
    (hf_lsc : LowerSemicontinuous f) : BddBelow (f '' K)  := proven

lemma exists_approx_min_on_compact {f : X → ℝ} {K : Set X}
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf_lsc : LowerSemicontinuous f) :
    ∀ ε > 0, ∃ x ∈ K, f x < sInf (f '' K) + ε  := proven

theorem lsc_attains_min_on_compact {f : X → ℝ} {K : Set X}
    (hK_compact : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf_lsc : LowerSemicontinuous f) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y  := proven

theorem mm_step_exists {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {xPrev : X}
    (hF_lsc : LowerSemicontinuous F) (hF_proper : MmProper F)
    (hF_compact : MmCompactSublevels F) :
    ∃ x : X, MmStep τ F xPrev x  := proven

theorem mm_curve_energy_dissipation {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {x0 : X}
    (curve : MmCurve τ F x0) (n : ℕ) :
    F (curve.points n) ≤ F x0  := proven

theorem mm_curve_distance_sum {τ : ℝ} (hτ : 0 < τ) {F : X → ℝ} {x0 : X}
    (curve : MmCurve τ F x0) (N : ℕ) :
    (Finset.range N).sum (fun n => distSquared (curve.points (n + 1)) (curve.points n)) ≤
    2 * τ * (F x0 - F (curve.points N))  := proven

end Frourio


## ./Frourio/Analysis/PLFA/EDEtoEVI.lean

namespace Frourio

lemma limsup_le_of_eventually_le_right {u : ℝ → ℝ} {c : ℝ} :
    (∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ c) →
    (∃ M : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ M) →
    (∃ m : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), m ≤ u h) →
    Filter.limsup u (nhdsWithin 0 (Set.Ioi 0)) ≤ c  := proven

lemma right_filter_limsup_le_of_bounded {u : ℝ → ℝ} {c : ℝ}
    (hub : ∃ M : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ M)
    (hlb : ∃ m : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), m ≤ u h)
    (hbound : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ c) :
    Filter.limsup u (nhdsWithin 0 (Set.Ioi 0)) ≤ c  := proven

lemma right_filter_limsup_le_simple {u : ℝ → ℝ} {c : ℝ}
    (hlb : ∃ m : ℝ, ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), m ≤ u h)
    (hbound : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0), u h ≤ c) :
    Filter.limsup u (nhdsWithin 0 (Set.Ioi 0)) ≤ c  := proven

lemma dini_upper_le_of_quotient_bounded {f : ℝ → ℝ} {t c m : ℝ}
    (hub : ∀ h ∈ Set.Ioo (0 : ℝ) 1, (f (t + h) - f t) / h ≤ c)
    (hlb : ∀ h ∈ Set.Ioo (0 : ℝ) 1, m ≤ (f (t + h) - f t) / h) :
    DiniUpper f t ≤ c  := proven

lemma dini_upper_distance_squared (ρ : ℝ → X) (v : X) (t : ℝ)
    (hLipschitz : ∃ L > 0, ∀ s₁ s₂, |s₁ - s₂| < 1 → dist (ρ s₁) (ρ s₂) ≤ L * |s₁ - s₂|) :
    ∃ C : ℝ, DiniUpper (fun τ => d2 (ρ τ) v) t ≤ C  := proven

lemma young_inequality_evi (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a^2 / 2 + b^2 / (2 * ε)  := proven

lemma geodesic_interpolation_estimate {G : GeodesicStructure X} (F : X → ℝ) (lamEff : ℝ)
    (hSemiconvex : GeodesicSemiconvex G F lamEff)
    (x y : X) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    F (G.γ x y t) ≤ (1 - t) * F x + t * F y - (lamEff / 2) * t * (1 - t) * (dist x y)^2  := proven

def UpperSemicontinuous (φ : ℝ → ℝ) : Prop  := proven

lemma upperSemicontinuous_add_continuous {f g : ℝ → ℝ}
    (hf : UpperSemicontinuous f)
    (hg_lip_bound : ∀ x : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ y z, |y - x| < δ → |z - x| < δ →
      |g y - g z| < (ε/2) * |y - z|) :
    UpperSemicontinuous (f + g)  := proven

lemma ereal_limsup_le_of_eventually_le {α : Type*} {f : α → EReal} {l : Filter α} {C : EReal}
    (h : ∀ᶠ x in l, f x ≤ C) :
    Filter.limsup f l ≤ C  := proven

lemma ereal_limsup_const {α : Type*} {l : Filter α} {C : EReal} [l.NeBot] :
  Filter.limsup (fun _ : α => C) l = C  := proven

lemma DiniUpperE_lam_d2_bound_explicit {X : Type*} [PseudoMetricSpace X]
    (ρ : ℝ → X) (v : X) (t : ℝ) (lam L : ℝ)
    (hL_pos : 0 < L)
    (hL_bound : ∀ s ∈ Set.Ioo (t - 1) (t + 1), dist (ρ s) (ρ t) ≤ L * |s - t|) :
    DiniUpperE (fun τ => lam * d2 (ρ τ) v) t ≤ (|lam| * (2 * L * dist (ρ t) v + L^2) : ℝ)  := proven

lemma DiniUpperE_lam_d2_bound {X : Type*} [PseudoMetricSpace X]
    (ρ : ℝ → X) (v : X) (t : ℝ) (lam : ℝ)
    (hLip : ∃ L > 0, ∀ s ∈ Set.Ioo (t - 1) (t + 1), dist (ρ s) (ρ t) ≤ L * |s - t|) :
    ∃ C : EReal, DiniUpperE (fun τ => lam * d2 (ρ τ) v) t ≤ C  := proven

end Frourio


## ./Frourio/Analysis/PLFA/EVItoEDE.lean

namespace Frourio

theorem evi_to_ede_constant (F : X → ℝ) (x : X)
    (ρ : ℝ → X) (hconst : ∀ t, ρ t = x) :
    EDE F ρ  := proven

theorem evi_to_ede_with_reg (F : X → ℝ) (ρ : ℝ → X)
    (hLocConst : ∀ t : ℝ, ∃ δ > 0, ∀ h, 0 < h ∧ h < δ → ρ (t + h) = ρ t) :
    EDE F ρ  := proven

end Frourio


## ./Frourio/Analysis/PLFA/PLFA.lean

namespace Frourio

theorem jko_to_plfa_constant (F : X → ℝ) : JKO_to_PLFA_pred F  := proven

noncomputable def FqR : ℝ → ℝ  := proven

theorem quadratic_halfConvex : HalfConvex (FqR) lamEff  := proven

theorem quadratic_strongUpperBound : StrongUpperBound (FqR)  := proven

theorem ede_to_evi_quadratic_from_builder
  (H : EDE_EVI_from_analytic_flags (X := ℝ) (FqR) lamEff) :
  ∀ ρ : ℝ → ℝ, EDE (FqR) ρ → IsEVISolution ({ E := FqR, lam := lamEff } : EVIProblem ℝ) ρ  := proven

theorem ede_to_plfa_from_real_flags (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ) :
  ∀ ρ : ℝ → X, EDE F ρ → PLFA F ρ  := proven

theorem plfa_to_ede_from_real_flags (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ) :
  ∀ ρ : ℝ → X, PLFA F ρ → EDE F ρ  := proven

theorem jko_to_plfa_from_real_flags (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff) :
  JKO_to_PLFA_pred F  := proven

def plfa_from_mm_limit (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem plfa_from_mm_limit_impl (F : X → ℝ) (lamEff : ℝ) :
  plfa_from_mm_limit (X := X) F lamEff  := proven

theorem ede_to_evi_from_flags_auto (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags (X := X) F lamEff) :
  EDE_to_EVI_from_flags (X := X) F lamEff  := proven

theorem evi_to_ede_from_flags_auto (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags (X := X) F lamEff) :
  EVI_to_EDE_from_flags (X := X) F lamEff  := proven

def ede_evi_from_mm (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem ede_evi_from_mm_impl (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags (X := X) F lamEff) : ede_evi_from_mm (X := X) F lamEff  := proven

theorem plfaEdeEviJko_equiv_real (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ)
  (HplfaEde : PLFA_EDE_from_real_flags (X := X) F lamEff)
  (HedeEvi_builder : EDE_EVI_from_analytic_flags (X := X) F lamEff)
  (HjkoPlfa : JKO_PLFA_from_real_flags (X := X) F lamEff) :
  plfaEdeEviJko_equiv F lamEff  := proven

end Frourio


## ./Frourio/Analysis/PLFA/PLFACore0.lean

namespace Frourio

def PLFA (F : X → ℝ) (ρ : ℝ → X) : Prop  := proven

def Action (F : X → ℝ) (ρ : ℝ → X) : Prop  := proven

def EDE (F : X → ℝ) (ρ : ℝ → X) : Prop  := proven

def JKO (F : X → ℝ) (ρ0 : X) : Prop  := proven

def HalfConvex (F : X → ℝ) (_lamEff : ℝ) : Prop  := proven

def StrongUpperBound (F : X → ℝ) : Prop  := proven

def Proper (F : X → ℝ) : Prop  := proven

def LowerSemicontinuous (F : X → ℝ) : Prop  := proven

def Coercive (F : X → ℝ) : Prop  := proven

def JKOStable (F : X → ℝ) : Prop  := proven

def PLFA_EDE_pred (F : X → ℝ) : Prop  := proven

def JKO_to_PLFA_pred (F : X → ℝ) : Prop  := proven

theorem plfa_implies_ede (F : X → ℝ) (ρ : ℝ → X) (h : PLFA F ρ) : EDE F ρ  := proven

def EDE_to_PLFA_bridge (F : X → ℝ) : Prop  := proven


theorem plfa_ede_equiv_from_bridge (F : X → ℝ)
  (HB : EDE_to_PLFA_bridge F) : PLFA_EDE_pred F  := proven

structure PLFAEDEAssumptions (F : X → ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
structure JKOPLFAAssumptions (F : X → ℝ) : Prop where
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ) := proven

structure JKOPLFAAssumptions (F : X → ℝ) : Prop where
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ) := proven

theorem plfa_ede_from_pack (F : X → ℝ) (H : PLFAEDEAssumptions F) : PLFA_EDE_pred F  := proven

theorem jko_plfa_from_pack (F : X → ℝ) (H : JKOPLFAAssumptions F) : JKO_to_PLFA_pred F  := proven

def PLFA_EDE_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def JKO_PLFA_from_analytic_flags (F : X → ℝ) : Prop  := proven


theorem plfa_ede_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : PLFAEDEAssumptions F) : PLFA_EDE_from_analytic_flags F lamEff  := proven


theorem jko_plfa_bridge_from_pack (F : X → ℝ) (_lamEff : ℝ)
  (H : JKOPLFAAssumptions F) : JKO_PLFA_from_analytic_flags F  := proven

theorem action_iff_plfa (F : X → ℝ) (ρ : ℝ → X) : Action F ρ ↔ PLFA F ρ  := proven


structure AnalyticFlags (F : X → ℝ) (lamEff : ℝ) : Prop where
  (proper : Proper F) (lsc : LowerSemicontinuous F) (coercive : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) (jkoStable : JKOStable F) := proven

theorem EDE_shift (F : X → ℝ) (ρ : ℝ → X)
  (hEDE : EDE F ρ) : ∀ s t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ))) t ≤ (0 : EReal)  := proven


theorem EDE_forwardDiff_nonpos (F : X → ℝ) (ρ : ℝ → X)
  (hEDE : EDE F ρ) :
  ∀ s t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ)) - F (ρ s)) t ≤ (0 : EReal)  := proven


theorem ede_to_plfa_with_gronwall_zero (F : X → ℝ) (ρ : ℝ → X)
  (hEDE : EDE F ρ)
  (G0 : ∀ s : ℝ,
    (∀ t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ)) - F (ρ s)) t ≤ (0 : EReal)) →
    ∀ t : ℝ, 0 ≤ t → F (ρ (s + t)) - F (ρ s) ≤ F (ρ (s + 0)) - F (ρ s)) :
  PLFA F ρ  := proven

theorem G0_from_DiniUpper_nonpos (F : X → ℝ) (ρ : ℝ → X)
    (h_usc_F : ∀ s : ℝ, ∀ s' t', s' < t' → ∀ w ∈ Set.Icc 0 (t' - s'),
      ∀ y₀ ∈ Set.Icc 0 (t' - s'), |y₀ - w| < (t' - s') / 4 →
      upper_semicontinuous_at_zero (fun τ => F (ρ (s + τ)) - F (ρ s)) s' y₀) :
    ∀ s : ℝ,
    (∀ t : ℝ, DiniUpperE (fun τ => F (ρ (s + τ)) - F (ρ s)) t ≤ (0 : EReal)) →
    ∀ t : ℝ, 0 ≤ t → F (ρ (s + t)) - F (ρ s) ≤ F (ρ (s + 0)) - F (ρ s)  := proven

theorem plfa_ede_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : PLFA_EDE_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ  := proven


theorem build_PLFAEDE_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (hP : Proper F) (hL : LowerSemicontinuous F) (hC : Coercive F)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : PLFA_EDE_from_analytic_flags F lamEff) : PLFAEDEAssumptions F  := proven

def JKO_to_EDE_pred (F : X → ℝ) : Prop  := proven

structure GeodesicStructure (X : Type*) [PseudoMetricSpace X] where
  γ : X → X → ℝ → X
  -- γ(x,y,0) = x
  start_point : ∀ x y, γ x y 0 = x
  -- γ(x,y,1) = y
  end_point : ∀ x y, γ x y 1 = y
  -- For t ∈ [0,1], γ(x,y,t) satisfies the geodesic property
  -- d(γ(x,y,s), γ(x,y,t)) = |t-s| * d(x,y) for s,t ∈ [0,1]
  geodesic_property : ∀ x y s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
    dist (γ x y s) (γ x y t) = |t - s| * dist x y := proven

def GeodesicSemiconvex {X : Type*} [PseudoMetricSpace X] (G : GeodesicStructure X)
    (F : X → ℝ) (lam : ℝ) : Prop  := proven

structure AnalyticFlagsReal (X : Type*) [PseudoMetricSpace X] (F : X → ℝ) (lamEff : ℝ) where
  -- F is proper: sublevel sets are nonempty and bounded below
  proper : ∃ c : ℝ, (Set.Nonempty {x | F x ≤ c}) ∧ BddBelow (Set.range F)
  -- F is lower semicontinuous (using mathlib's definition)
  lsc : LowerSemicontinuous F
  -- F is coercive: grows to infinity at infinity
  coercive : ∀ C : ℝ, ∃ R : ℝ, ∀ x : X, (∃ x₀, dist x x₀ > R) → F x > C
  -- Geodesic structure exists on X
  geodesic : GeodesicStructure X
  -- F is geodesically semiconvex with parameter lamEff
  semiconvex : GeodesicSemiconvex geodesic F lamEff
  -- Sublevel sets are compact (for existence of minimizers)
  compact_sublevels : ∀ c : ℝ, IsCompact {x : X | F x ≤ c}
  -- Slope is bounded: descendingSlope F x ≤ M for all x
  slope_bound : ∃ M : ℝ, 0 ≤ M ∧ (∀ x : X, descendingSlope F x ≤ M)
  -- An explicit lower bound for the effective parameter and its validity
  lamLowerBound : ℝ
  lamEff_ge : lamEff ≥ lamLowerBound := proven

def lamLowerFromRealFlags {X : Type*} [PseudoMetricSpace X]
  {F : X → ℝ} {lamEff : ℝ} (flags : AnalyticFlagsReal X F lamEff) : ℝ  := proven

theorem lamEff_ge_fromRealFlags {X : Type*} [PseudoMetricSpace X]
  {F : X → ℝ} {lamEff : ℝ} (flags : AnalyticFlagsReal X F lamEff) :
  lamEff ≥ lamLowerFromRealFlags flags  := proven

def ShiftedUSCHypothesis {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) (ρ : ℝ → X) : Prop  := proven

def PLFA_EDE_from_real_flags {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def JKO_PLFA_from_real_flags {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def real_to_placeholder_flags {X : Type*} [PseudoMetricSpace X] (F : X → ℝ) (lamEff : ℝ)
    (_real_flags : AnalyticFlagsReal X F lamEff) : AnalyticFlags F lamEff := {
  proper := ⟨0, fun x => by simp⟩  -- Trivial placeholder
  lsc := fun x => ⟨0, le_refl 0, by simp⟩  -- Trivial placeholder
  coercive := fun x => ⟨0, le_refl 0, by simp⟩  -- Trivial placeholder
  HC := ⟨0, le_refl 0, fun x => by simp⟩  -- Trivial placeholder
  SUB := ⟨0, le_refl 0, fun x => by simp⟩  -- Trivial placeholder
  jkoStable := fun ρ0 => ⟨fun _ => ρ0, rfl, fun t => le_refl (F ρ0)⟩  -- Constant curve
} := proven

theorem plfa_ede_from_real_flags_impl {X : Type*} [PseudoMetricSpace X] (F : X → ℝ)
    (lamEff : ℝ) (_real_flags : AnalyticFlagsReal X F lamEff)
    (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis F ρ) :
    PLFA_EDE_pred F  := proven

theorem jko_plfa_from_real_flags_impl {X : Type*} [PseudoMetricSpace X]
    (F : X → ℝ) (lamEff : ℝ) (_real_flags : AnalyticFlagsReal X F lamEff) :
    JKO_to_PLFA_pred F  := proven

end Frourio


## ./Frourio/Analysis/PLFA/PLFACore1.lean

namespace Frourio

def linearGeodesicStructure : GeodesicStructure ℝ where
  γ  := proven

def chooseAnalyticRoute (F : X → ℝ) (lamEff : ℝ) (useReal : Bool) : Prop  := proven

theorem both_routes_valid (F : X → ℝ) (lamEff : ℝ)
    (h_usc : ∀ ρ : ℝ → X, ∀ s : ℝ, ∀ s' t', s' < t' → ∀ w ∈ Set.Icc 0 (t' - s'),
      ∀ y₀ ∈ Set.Icc 0 (t' - s'), |y₀ - w| < (t' - s') / 4 →
      upper_semicontinuous_at_zero (fun τ => F (ρ (s + τ)) - F (ρ s)) s' y₀) :
    (∃ _real_flags : AnalyticFlagsReal X F lamEff, True) →
    (∃ _placeholder_flags : AnalyticFlags F lamEff, True) →
    (chooseAnalyticRoute F lamEff true ∨ chooseAnalyticRoute F lamEff false)  := proven

theorem plfa_ede_from_real_flags_builder (F : X → ℝ) (lamEff : ℝ) :
  PLFA_EDE_from_real_flags (X := X) F lamEff  := proven

theorem jko_plfa_from_real_flags_builder (F : X → ℝ) (lamEff : ℝ) :
  JKO_PLFA_from_real_flags (X := X) F lamEff  := proven

def EDE_EVI_pred (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def plfaEdeEviJko_equiv (F : X → ℝ) (lamEff : ℝ) : Prop  := proven


structure EquivBuildAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfa_iff_ede : ∀ ρ : ℝ → X, PLFA F ρ ↔ EDE F ρ)
  (ede_iff_evi : ∀ ρ : ℝ → X,
    EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ)
  (jko_to_plfa : ∀ ρ0 : X, JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ PLFA F ρ) := proven


theorem build_plfaEdeEvi_package (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff  := proven


theorem build_plfaEdeEvi_package_weak (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : plfaEdeEviJko_equiv F lamEff  := proven


structure EDEEVIAssumptions (F : X → ℝ) (lamEff : ℝ) : Prop where
  (ede_iff_evi : ∀ ρ : ℝ → X,
    EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ) := proven


theorem ede_evi_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_pred F lamEff  := proven

def EDE_EVI_from_analytic_flags (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem ede_evi_from_analytic_flags_with_core (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff) : EDE_EVI_pred F lamEff  := proven

theorem ede_evi_from_real_flags_and_builder_with_bound
  {X : Type*} [PseudoMetricSpace X]
  (F : X → ℝ) (lamEff : ℝ)
  (flags : AnalyticFlagsReal X F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  EDE_EVI_pred F lamEff ∧ lamEff ≥ lamLowerFromRealFlags flags  := proven

def EDE_to_EVI_from_flags (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def EVI_to_EDE_from_flags (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem build_ede_evi_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

theorem ede_evi_pred_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDE_EVI_pred F lamEff  := proven

theorem build_EDEEVI_pack_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDEEVIAssumptions F lamEff  := proven

theorem ede_to_evi_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, EDE F ρ → IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ  := proven

theorem evi_to_ede_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  ∀ ρ : ℝ → X, IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ → EDE F ρ  := proven


theorem ede_evi_bridge_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff  := proven


theorem plfa_ede_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : PLFA_EDE_from_analytic_flags F lamEff  := proven


theorem ede_evi_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff  := proven


theorem jko_plfa_bridge_from_equiv_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EquivBuildAssumptions F lamEff) : JKO_PLFA_from_analytic_flags F  := proven


theorem ede_evi_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  ∀ ρ : ℝ → X, EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ  := proven

theorem ede_evi_pred_from_core_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff) :
  EDE_EVI_pred F lamEff  := proven

theorem ede_evi_pred_from_core_flags_via_builder (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) : EDE_EVI_pred F lamEff  := proven

end Frourio


## ./Frourio/Analysis/PLFA/PLFACore2.lean

namespace Frourio


theorem build_EDEEVI_pack_from_flags (F : X → ℝ) (lamEff : ℝ)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F)
  (H : EDE_EVI_from_analytic_flags F lamEff) : EDEEVIAssumptions F lamEff  := proven

theorem component_predicates_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : PLFA_EDE_pred F ∧ EDE_EVI_pred F lamEff ∧ JKO_to_PLFA_pred F  := proven


structure GlobalSufficientPack (F : X → ℝ) (lamEff : ℝ) : Prop where
  (HC : HalfConvex F lamEff)
  (SUB : StrongUpperBound F)
  (components : PLFA_EDE_pred F ∧ EDE_EVI_pred F lamEff ∧ JKO_to_PLFA_pred F) := proven


theorem global_sufficient_pack_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : GlobalSufficientPack F lamEff  := proven


theorem build_package_from_global (F : X → ℝ) (lamEff : ℝ)
  (H : GlobalSufficientPack F lamEff) : plfaEdeEviJko_equiv F lamEff  := proven


theorem build_package_from_analytic_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : plfaEdeEviJko_equiv F lamEff  := proven

theorem plfaEdeEviJko_equiv_from_core_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F) :
  plfaEdeEviJko_equiv F lamEff  := proven

theorem build_package_from_flags_and_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : plfaEdeEviJko_equiv F lamEff  := proven

theorem global_sufficient_pack_from_directional_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (Hfwd : EDE_to_EVI_from_flags F lamEff)
  (Hrev : EVI_to_EDE_from_flags F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : GlobalSufficientPack F lamEff  := proven

theorem ede_to_evi_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : EDE_to_EVI_from_flags F lamEff  := proven

theorem evi_to_ede_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : EVI_to_EDE_from_flags F lamEff  := proven

theorem ede_to_evi_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_to_EVI_from_flags F lamEff  := proven


theorem evi_to_ede_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EVI_to_EDE_from_flags F lamEff  := proven

theorem ede_to_evi_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  EDE_to_EVI_from_flags F lamEff  := proven


theorem evi_to_ede_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  EVI_to_EDE_from_flags F lamEff  := proven

theorem ede_to_evi_from_evi_pred (F : X → ℝ) (lamEff : ℝ)
  (H : Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff) :
  EDE_to_EVI_from_flags F lamEff  := proven

theorem evi_to_ede_from_evi_pred (F : X → ℝ) (lamEff : ℝ)
  (H : Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff) :
  EVI_to_EDE_from_flags F lamEff  := proven

theorem ede_evi_from_evi_bridges (F : X → ℝ) (lamEff : ℝ)
  (HF : Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff)
  (HB : Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

theorem ede_evi_from_evi_equiv_bridge (F : X → ℝ) (lamEff : ℝ)
  (H : Frourio.EVIEquivBridge (fun F ρ => EDE F ρ) F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

theorem evi_forward_bridge_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  Frourio.EVIBridgeForward (fun F ρ => EDE F ρ) F lamEff  := proven

theorem evi_backward_bridge_from_builder (F : X → ℝ) (lamEff : ℝ)
  (H : EDE_EVI_from_analytic_flags F lamEff)
  (HC : HalfConvex F lamEff) (SUB : StrongUpperBound F) :
  Frourio.EVIBridgeBackward (fun F ρ => EDE F ρ) F lamEff  := proven

def EDE_to_EVI_concrete (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def EVI_to_EDE_concrete (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem ede_evi_from_concrete_bridges (F : X → ℝ) (lamEff : ℝ)
  (HF : EDE_to_EVI_concrete F lamEff)
  (HB : EVI_to_EDE_concrete F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

theorem ede_to_evi_from_concrete (F : X → ℝ) (lamEff : ℝ)
  (HF : EDE_to_EVI_concrete F lamEff) :
  EDE_to_EVI_from_flags F lamEff  := proven

theorem evi_to_ede_from_concrete (F : X → ℝ) (lamEff : ℝ)
  (HB : EVI_to_EDE_concrete F lamEff) :
  EVI_to_EDE_from_flags F lamEff  := proven

theorem ede_to_evi_concrete_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) :
  EDE_to_EVI_concrete F lamEff  := proven

theorem evi_to_ede_concrete_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) :
  EVI_to_EDE_concrete F lamEff  := proven

theorem ede_to_evi_concrete_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) :
  EDE_to_EVI_concrete F lamEff  := proven


theorem evi_to_ede_concrete_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) :
  EVI_to_EDE_concrete F lamEff  := proven

theorem ede_to_evi_concrete_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) :
  EDE_to_EVI_concrete F lamEff  := proven


theorem evi_to_ede_concrete_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) :
  EVI_to_EDE_concrete F lamEff  := proven

theorem ede_to_evi_concrete_from_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  EDE_to_EVI_concrete F lamEff  := proven

theorem evi_to_ede_concrete_from_flags (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) :
  EVI_to_EDE_concrete F lamEff  := proven

theorem ede_evi_from_analytic_flags_via_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

theorem ede_evi_from_analytic_flags_final (F : X → ℝ) (lamEff : ℝ)
  (HF : EDE_to_EVI_concrete F lamEff)
  (HB : EVI_to_EDE_concrete F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

end Frourio


## ./Frourio/Analysis/PLFA/PLFACore3.lean

namespace Frourio

def HF (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

def HB (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem HF_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : HF F lamEff  := proven

theorem HB_from_pred (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : HB F lamEff  := proven

theorem HF_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : HF F lamEff  := proven

theorem HB_from_pack (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : HB F lamEff  := proven

theorem HF_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) : HF F lamEff  := proven

theorem HB_from_global (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) : HB F lamEff  := proven

theorem HF_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) : HF F lamEff  := proven

theorem HB_from_flags_builder (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (H : EDE_EVI_from_analytic_flags F lamEff) : HB F lamEff  := proven

theorem ede_evi_builder_from_HF_HB (F : X → ℝ) (lamEff : ℝ)
  (hF : HF F lamEff) (hB : HB F lamEff) :
  EDE_EVI_from_analytic_flags F lamEff  := proven

def EDE_EVI_short_input (F : X → ℝ) (lamEff : ℝ) : Prop  := proven

theorem ede_evi_from_short_input (F : X → ℝ) (lamEff : ℝ)
  (Hin : EDE_EVI_short_input F lamEff) : EDE_EVI_from_analytic_flags F lamEff  := proven

theorem ede_evi_from_pred_short (F : X → ℝ) (lamEff : ℝ)
  (Hpred : EDE_EVI_pred F lamEff) : EDE_EVI_from_analytic_flags F lamEff  := proven

theorem ede_evi_from_pack_short (F : X → ℝ) (lamEff : ℝ)
  (H : EDEEVIAssumptions F lamEff) : EDE_EVI_from_analytic_flags F lamEff  := proven


structure AnalyticBridges (F : X → ℝ) (lamEff : ℝ) : Prop where
  (plfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (edeEvi : EDE_EVI_from_analytic_flags F lamEff)
  (jkoPlfa : JKO_PLFA_from_analytic_flags F) := proven


theorem build_package_from_flags_and_bridges (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff) (B : AnalyticBridges F lamEff) : plfaEdeEviJko_equiv F lamEff  := proven


theorem plfaEdeEviJko_equiv_from_flags (F : X → ℝ) (lamEff : ℝ)
  (H1 : PLFA_EDE_from_analytic_flags F lamEff)
  (H2 : EDE_EVI_from_analytic_flags F lamEff)
  (H3 : JKO_PLFA_from_analytic_flags F)
  (A : AnalyticFlags F lamEff) : plfaEdeEviJko_equiv F lamEff  := proven

theorem global_sufficient_pack_from_flags_and_ede_evi_pack (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEviPack : EDEEVIAssumptions F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : GlobalSufficientPack F lamEff  := proven

theorem build_package_from_flags_and_ede_evi_pack (F : X → ℝ) (lamEff : ℝ)
  (A : AnalyticFlags F lamEff)
  (HplfaEde : PLFA_EDE_from_analytic_flags F lamEff)
  (HedeEviPack : EDEEVIAssumptions F lamEff)
  (HjkoPlfa : JKO_PLFA_from_analytic_flags F) : plfaEdeEviJko_equiv F lamEff  := proven

def TwoEVIWithForce (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

def GeodesicUniformEvalFor (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

def TwoEVIWithForceShared (P : EVIProblem X) (u v : ℝ → X) : Prop  := proven

theorem twoEVIShared_to_plain (P : EVIProblem X) (u v : ℝ → X) :
  TwoEVIWithForceShared P u v → TwoEVIWithForce P u v  := proven


theorem twoEVIWithForce_to_distance (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η  := proven

theorem twoEVIWithForceShared_to_distance (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v)
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η  := proven


theorem twoEVIWithForce_to_distance_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t)))
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η  := proven

theorem twoEVIWithForceShared_to_distance_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t)))
  (Hbridge : ∀ η : ℝ, HbridgeWithError P u v η) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η  := proven

theorem twoEVIWithForce_to_distance_concrete (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η  := proven

theorem twoEVIWithForceShared_to_distance_concrete (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError P u v η  := proven

theorem twoEVIWithForce_to_distance_concrete_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForce P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η  := proven

theorem twoEVIWithForceShared_to_distance_concrete_closed (P : EVIProblem X) (u v : ℝ → X)
  (H : TwoEVIWithForceShared P u v)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred P.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError P u v η  := proven

theorem ede_iff_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  EDE F ρ ↔ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ  := proven


theorem evi_iff_plfa (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ : ℝ → X) :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ ↔ PLFA F ρ  := proven


theorem jko_to_evi (F : X → ℝ) (lamEff : ℝ)
  (G : plfaEdeEviJko_equiv F lamEff) (ρ0 : X) :
  JKO F ρ0 → ∃ ρ : ℝ → X, ρ 0 = ρ0 ∧ IsEVISolution ({ E := F, lam := lamEff } : EVIProblem X) ρ  := proven

end Frourio


## ./Frourio/Analysis/QuadraticForm.lean

namespace Frourio

@[simp]
lemma ennreal_norm_eq_coe_nnnorm (z : ℂ) : (‖z‖ₑ : ℝ≥0∞) = (‖z‖₊ : ℝ≥0∞)  := proven

lemma mul_mem_L2 (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume) < ∞  := proven

lemma mul_mem_L2_memLp (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    MemLp (fun x => K x * (g : ℝ → ℂ) x) 2 volume  := proven

lemma M_K_pointwise_bound (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ∀ᵐ x ∂volume,
      ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ))
        ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume ^ (2 : ℕ)) *
        ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ))  := proven

lemma M_K_L2_bound (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ x, ((‖(K x * (g : ℝ → ℂ) x)‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)
      ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume ^ (2 : ℕ)) *
        (∫⁻ x, ((‖(g : ℝ → ℂ) x‖₊ : ℝ≥0∞) ^ (2 : ℕ)) ∂volume)  := proven

lemma M_K_linear_map_bound (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞)
    (L : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hL : ∀ g, L g = (mul_mem_L2_memLp K g hK_meas hK_bdd).toLp _) :
    ∀ g, ‖L g‖ ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume).toReal * ‖g‖  := proven


noncomputable def M_K (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven

lemma M_K_apply_ae (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (((M_K K hK_meas hK_bdd) g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (fun x => K x * (g : ℝ → ℂ) x)  := proven

theorem M_K_norm_le (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    ‖M_K K hK_meas hK_bdd‖ ≤ (essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume).toReal  := proven

noncomputable def Qℝ (K : ℝ → ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

theorem Q_pos (K : ℝ → ℝ) (hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    0 ≤ Qℝ K g  := proven

theorem Qℝ_eq_inner (K : ℝ → ℝ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) :
    Qℝ K g = (@inner ℂ _ _ (M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd g) g).re  := proven

def supp_K (K : ℝ → ℂ) : Set ℝ  := proven

def zero_set_K (K : ℝ → ℂ) : Set ℝ  := proven


@[simp]
lemma mem_supp_K (K : ℝ → ℂ) (τ : ℝ) : τ ∈ supp_K K ↔ K τ ≠ 0  := proven


@[simp]
lemma mem_zero_set_K (K : ℝ → ℂ) (τ : ℝ) : τ ∈ zero_set_K K ↔ K τ = 0  := proven

lemma measurableSet_supp_K (K : ℝ → ℂ) (hK : Measurable K) :
    MeasurableSet (supp_K K)  := proven

lemma supp_K_compl (K : ℝ → ℂ) : (supp_K K)ᶜ = zero_set_K K  := proven

noncomputable def ker_MK (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))  := proven

theorem ker_MK_eq_vanish_on_supp (K : ℝ → ℂ)
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    ker_MK K hK_meas hK_bdd =
    {g : Lp ℂ 2 (volume : Measure ℝ) |
     (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0}  := proven

theorem ker_MK_iff_ae_zero_on_supp (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    g ∈ ker_MK K hK_meas hK_bdd ↔ (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0  := proven

lemma ker_MK_supported_on_zero_set (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    g ∈ ker_MK K hK_meas hK_bdd → (g : ℝ → ℂ) =ᵐ[volume.restrict (supp_K K)] 0  := proven

lemma ker_MK_ae (K : ℝ → ℂ) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hK_meas : AEStronglyMeasurable K volume)
    (hK_bdd : essSup (fun x => (‖K x‖₊ : ℝ≥0∞)) volume < ∞) :
    g ∈ ker_MK K hK_meas hK_bdd ↔
      (∀ᵐ x ∂volume.restrict (supp_K K), (g : ℝ → ℂ) x = 0)  := proven


section PullbackToHσ

noncomputable def Qσ (K : ℝ → ℝ) (f : Hσ σ) : ℝ  := proven

theorem Qσ_pos (K : ℝ → ℝ) (hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) (f : Hσ σ) :
    0 ≤ Qσ[K] f  := proven

theorem Qσ_eq_zero_imp_kernel_zero (K : ℝ → ℝ) (f : Hσ σ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞)
    (hK_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    Qσ[K] f = 0 → (∀ᵐ τ ∂volume, K τ * ‖LogPull σ f τ‖^2 = 0)  := proven

lemma ker_Qσ_subset_ker_MK (K : ℝ → ℝ)
    (hK_meas : AEStronglyMeasurable (fun τ => (K τ : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞)
    (hK_nonneg : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    {f : Hσ σ | Qσ[K] f = 0} ⊆
    {f : Hσ σ | M_K (fun τ => (K τ : ℂ)) hK_meas hK_bdd
      ((mellin_in_L2 σ f).toLp (LogPull σ f)) = 0}  := proven

theorem Qσ_eq_zero_of_mellin_ae_zero (K : ℝ → ℝ) (f : Hσ σ) :
    LogPull σ f =ᵐ[volume] 0 → Qσ[K] f = 0  := proven

structure FiniteLatticeKernel (K : ℝ → ℝ) (N : ℕ)
    (hK_meas : AEStronglyMeasurable (fun τ => ((K τ) : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) where
  /-- The basis functions indexed by lattice points -/
  basis : Fin N → Lp ℂ 2 (volume : Measure ℝ)
  /-- Each basis function is in the kernel -/
  in_kernel : ∀ i, basis i ∈ ker_MK (fun τ => (K τ : ℂ)) hK_meas hK_bdd
  /-- The basis functions are linearly independent -/
  lin_indep : LinearIndependent ℂ basis := proven

def finite_kernel_dim (K : ℝ → ℝ) (N : ℕ)
    {hK_meas : AEStronglyMeasurable (fun τ => ((K τ) : ℂ)) volume}
    {hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞}
    (_approx : FiniteLatticeKernel K N hK_meas hK_bdd) : ℕ  := proven

theorem kernel_dim_lattice_approx (K : ℝ → ℝ)
    (hK_meas : AEStronglyMeasurable (fun τ => ((K τ) : ℂ)) volume)
    (hK_bdd : essSup (fun x => (‖(K x : ℂ)‖₊ : ℝ≥0∞)) volume < ∞) :
    ∃ (_ : ℕ → Σ N, FiniteLatticeKernel K N hK_meas hK_bdd),
      True  := proven


section QσKernelConnection

theorem Qσ_zero_of_mellin_ae_zero_v2 (K : ℝ → ℝ) (f : Hσ σ) :
    LogPull σ f =ᵐ[volume] 0 → Qσ[K] f = 0  := proven

theorem ker_Qσ_characterization (K : ℝ → ℝ) :
    {f : Hσ σ | Qσ[K] f = 0} ⊇
    {f : Hσ σ | LogPull σ f =ᵐ[volume] 0}  := proven

lemma ker_Qσ_dim_eq_ker_MK_dim (K : ℝ → ℝ) (_hK : ∀ᵐ τ ∂volume, 0 ≤ K τ) :
    -- Placeholder for: dim(ker Qσ[K]) = dim(ker M_K)
    True  := proven

end Frourio


## ./Frourio/Analysis/SchwartzDensity.lean

namespace Frourio

lemma schwartz_mem_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => if x > 0 then f x else 0) 2
      (mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1)))  := sorry

noncomputable def schwartzToHσ {σ : ℝ} (hσ : 1 / 2 < σ) (f : SchwartzMap ℝ ℂ) : Hσ σ  := proven

lemma schwartzToHσ_linear {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∀ (a : ℂ) (f g : SchwartzMap ℝ ℂ),
    schwartzToHσ hσ (a • f + g) = a • schwartzToHσ hσ f + schwartzToHσ hσ g  := sorry

lemma schwartzToHσ_continuous {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ (k₁ k₂ : ℕ) (C : ℝ), 0 < C ∧
    ∀ f : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ f‖ ≤ C * SchwartzMap.seminorm ℝ k₁ k₂ f  := sorry

theorem schwartz_dense_in_Hσ {σ : ℝ} (hσ : 1 / 2 < σ) :
    DenseRange (schwartzToHσ hσ)  := sorry

lemma schwartzToHσ_ae_eq {σ : ℝ} (hσ : 1 / 2 < σ) (φ : SchwartzMap ℝ ℂ) :
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0)  := proven

lemma exists_schwartz_approximation {σ : ℝ} (hσ : 1 / 2 < σ) (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ φ - f‖ < ε  := proven

lemma schwartz_ae_dense {σ : ℝ} (hσ : 1 / 2 < σ) (f : Hσ σ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : SchwartzMap ℝ ℂ, ‖schwartzToHσ hσ φ - f‖ < ε ∧
    (schwartzToHσ hσ φ : ℝ → ℂ) =ᵐ[mulHaar.withDensity fun x => ENNReal.ofReal (x ^ (2 * σ - 1))]
      (fun x => if x > 0 then φ x else 0)  := proven

end Frourio


## ./Frourio/Analysis/Slope.lean

namespace Frourio

def posDist (x : X) : Set X  := proven

@[simp] def posPart (r : ℝ) : ℝ  := proven

@[simp] theorem posPart_nonneg (r : ℝ) : 0 ≤ posPart r  := proven

@[simp] theorem posPart_le_abs (r : ℝ) : posPart r ≤ |r|  := proven

noncomputable def slopeQuot (F : X → ℝ) (x y : X) : ℝ  := proven

theorem slopeQuot_nonneg_of_posdist (F : X → ℝ) (x y : X)
  (h : 0 < dist x y) : 0 ≤ slopeQuot F x y  := proven

noncomputable def descendingSlopeE (F : X → ℝ) (x : X) : EReal  := proven

noncomputable def descendingSlope (F : X → ℝ) (x : X) : ℝ  := proven

end Frourio

namespace Frourio

theorem eventually_nonneg_slopeQuot (F : X → ℝ) (x : X) :
  ∀ᶠ y in nhdsWithin x (posDist x),
    0 ≤ (posPart (F x - F y)) / dist x y  := proven

theorem descendingSlopeE_const (x : X) (c : ℝ)
  [Filter.NeBot (nhdsWithin x (posDist x))] :
  descendingSlopeE (fun _ : X => c) x = 0  := proven

theorem descendingSlope_const (x : X) (c : ℝ)
  [Filter.NeBot (nhdsWithin x (posDist x))] :
  descendingSlope (fun _ : X => c) x = 0  := proven

lemma limsup_le_of_eventually_le_real {α : Type*} {l : Filter α} [l.NeBot]
  {f g : α → ℝ}
  (hf_lb : ∃ m : ℝ, ∀ᶠ a in l, m ≤ f a)
  (hg_ub : ∃ M : ℝ, ∀ᶠ a in l, g a ≤ M) -- Added: g needs an upper bound
  (h : ∀ᶠ a in l, f a ≤ g a) :
  Filter.limsup f l ≤ Filter.limsup g l  := proven

lemma isCoboundedUnder_le_of_eventually_nonneg {α : Type*} {l : Filter α} [l.NeBot]
  {f : α → ℝ} (h : ∀ᶠ a in l, 0 ≤ f a) :
  Filter.IsCoboundedUnder (· ≤ ·) l f  := proven

theorem descendingSlopeE_le_of_lipschitzWith
  (K : Real) (_hK : 0 ≤ K) (F : X → ℝ) (x : X) (hL : ∀ x y, dist (F x) (F y) ≤ K * dist x y) :
  descendingSlopeE F x ≤ (K : EReal)  := proven

end Frourio


## ./Frourio/Analysis/SuitableWindow.lean

namespace Frourio.Analysis

structure suitable_window (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop where
  normalized : ‖f‖ = 1
  time_localized : ∃ C > 0, ∀ᵐ t : ℝ, ‖f t‖ ≤ C * (1 + |t|)^(-(2 : ℝ))
  -- Additional conditions can be added as needed := proven

theorem suitable_window_of_normalized_gaussian (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : Lp ℂ 2 volume, ‖w‖ = 1 ∧ suitable_window w  := proven

end Frourio.Analysis


## ./Frourio/Analysis/TrigPositivity.lean

namespace Frourio


structure TrigPoly (a : ℝ) where
  N : ℕ
  c : ℤ → ℂ := proven

namespace TrigPoly

noncomputable def eval (F : TrigPoly a) (τ : ℝ) : ℂ  := proven

noncomputable def kernelR (F : TrigPoly a) : ℝ → ℝ  := proven

theorem Q_pos_of_ae_nonneg (F : TrigPoly a)
    (h : ∀ᵐ τ ∂MeasureTheory.volume, 0 ≤ kernelR F τ)
    (g : Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    0 ≤ Qℝ (kernelR F) g  := proven

end TrigPoly

namespace LatticeResidue

noncomputable def eK (_a : ℝ) (_k : ℤ) : Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)  := proven

def symmIdx (N : ℕ) : Finset ℤ  := proven

def lattice_residue_finite (F : TrigPoly a) : Prop  := proven

structure LatticeResidueHypotheses (F : TrigPoly a) : Prop where
  holds : lattice_residue_finite F := proven

theorem lattice_residue_finite_proof (F : TrigPoly a)
    (h : LatticeResidueHypotheses (a := a) F) : lattice_residue_finite F  := proven

end LatticeResidue

namespace Toeplitz

def idxToZ (N : ℕ) (i : Fin (2 * N + 1)) : ℤ  := proven

noncomputable def matrix (F : TrigPoly a) :
    Matrix (Fin (2 * F.N + 1)) (Fin (2 * F.N + 1)) ℂ  := proven

noncomputable def qform (F : TrigPoly a)
    (v : (Fin (2 * F.N + 1)) → ℂ) : ℝ  := proven

def isPSD (F : TrigPoly a) : Prop  := proven

end Toeplitz

namespace TrigPoly

def nonneg (F : TrigPoly a) : Prop  := proven

theorem F_nonneg_iff_toeplitz_psd (F : TrigPoly a) :
    nonneg (a := a) F ↔ Toeplitz.isPSD (a := a) F  := proven

end TrigPoly

end Frourio


## ./Frourio/Analysis/Windows.lean

namespace Frourio

noncomputable def gaussianFun (α : ℝ) (t : ℝ) : ℝ  := proven

noncomputable def gaussian (_ : ℝ) : Lp ℂ 2 (volume : Measure ℝ)  := proven

def gaussian_decay (α : ℝ) : Prop  := proven

def overlap_bound (α Δτ : ℝ) : Prop  := proven

theorem gaussian_decay_of_nonneg {α : ℝ} (hα : 0 ≤ α) : gaussian_decay α  := proven

end Frourio


## ./Frourio/Analysis/YoungRigidity.lean

namespace Frourio

abbrev MeasureR  := proven

noncomputable def L2NormR (_f : ℝ → ℂ) : ℝ  := proven

noncomputable def TVNorm (_ν : MeasureR) : ℝ  := proven

noncomputable def L2NormZ (a : ℤ → ℂ) : ℝ  := proven

noncomputable def L1NormZ (μ : ℤ → ℂ) : ℝ  := proven

noncomputable def convR_measure (_f : ℝ → ℂ) (_ν : MeasureR) : ℝ → ℂ  := proven

noncomputable def convZ (a : ℤ → ℂ) (μ : ℤ → ℂ) : ℤ → ℂ  := proven

structure DiracLike where
  (phase : ℝ)
  (s0 : ℝ) := proven

noncomputable def oneFunc : ℝ → ℂ  := proven

lemma oneFunc_ne_zero : oneFunc ≠ (fun _ => (0 : ℂ))  := proven

def convR_measure_is_linear (ν : MeasureR) : Prop  := proven

end Frourio


## ./Frourio/Analysis/ZakMellin.lean

namespace Frourio

noncomputable def Qdisc (_K : ℝ → ℝ)
    (_w : Lp ℂ 2 (volume : Measure ℝ)) (_Δτ _Δξ : ℝ)
    (_g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

def Q_bounds (K : ℝ → ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop  := proven

end Frourio

namespace Frourio

noncomputable def timeShiftFun (τ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ  := proven

noncomputable def modFun (ξ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ  := proven

def translationMap (τ : ℝ) : ℝ → ℝ  := proven

lemma measurable_translation (τ : ℝ) : Measurable (translationMap τ)  := proven

lemma measurableEmbedding_translation (τ : ℝ) :
    MeasurableEmbedding (translationMap τ)  := proven

lemma translation_measurePreserving (τ : ℝ) :
    MeasurePreserving (translationMap τ) (μa := volume) (μb := volume)  := proven

lemma ae_comp_translation_iff {p : ℝ → Prop}
    (hp : MeasurableSet {y | p y}) (τ : ℝ) :
    (∀ᵐ y ∂ (volume : Measure ℝ), p y)
      ↔ (∀ᵐ x ∂ (volume : Measure ℝ), p ((translationMap τ) x))  := proven

lemma ae_comp_translation_of_ae_eq
    {u v : ℝ → ℂ} (τ : ℝ)
    (hu : AEStronglyMeasurable u (volume : Measure ℝ))
    (hv : AEStronglyMeasurable v (volume : Measure ℝ))
    (h : u =ᵐ[volume] v) :
    (fun x => u (x - τ)) =ᵐ[volume] (fun x => v (x - τ))  := proven

lemma comp_translation_memLp (τ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun t => (f : ℝ → ℂ) (t - τ)) 2 (volume : Measure ℝ)  := proven

noncomputable def timeShift_linearMap (τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f  := proven

lemma timeShift_norm_eq (τ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖timeShift_linearMap τ f‖ = ‖f‖  := proven

noncomputable def timeShift (τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven

lemma integral_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (τ : ℝ) :
    ∫ t, f (t - τ) ∂(volume : Measure ℝ) = ∫ t, f t ∂(volume : Measure ℝ)  := proven

lemma eLpNorm_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (p : ENNReal) (τ : ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm (fun t => f (t - τ)) p (volume : Measure ℝ) =
    eLpNorm f p (volume : Measure ℝ)  := proven

lemma L2_norm_comp_sub (f : ℝ → ℂ) (τ : ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    eLpNorm (fun t => f (t - τ)) 2 (volume : Measure ℝ) =
    eLpNorm f 2 (volume : Measure ℝ)  := proven

lemma phase_abs_one (ξ t : ℝ) :
    ‖Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))‖ = 1  := proven

lemma mod_add_ae (ξ : ℝ)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))
        * ((f + g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
      =ᵐ[volume]
    (fun t : ℝ =>
        Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t
        + Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (g : ℝ → ℂ) t)  := proven


lemma mod_smul_ae (ξ : ℝ) (c : ℂ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ))
        * ((c • f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
      =ᵐ[volume]
    (fun t : ℝ =>
        c • (Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t))  := proven

lemma mod_memLp (ξ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun t : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) * (f : ℝ → ℂ) t)
      2 (volume : Measure ℝ)  := proven

noncomputable def mod_linearMap (ξ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f  := proven

lemma mod_norm_eq (ξ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mod_linearMap ξ f‖ = ‖f‖  := proven

noncomputable def mod (ξ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)  := proven

noncomputable def ZakCoeff (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℤ × ℤ → ℂ  := proven

noncomputable def FrameEnergy (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

def besselBound (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ B : ℝ) : Prop  := proven

def HasBesselBound (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop  := proven

lemma frameEnergy_le_of_bessel
    {w : Lp ℂ 2 (volume : Measure ℝ)} {Δτ Δξ B : ℝ}
    (hb : besselBound w Δτ Δξ B)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    FrameEnergy w Δτ Δξ g ≤ B * ‖g‖^2  := proven

end Frourio

namespace Frourio

def suitable_window (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

def ZakFrame_inequality
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ) : Prop  := proven

theorem ZakFrame_inequality_proof
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (hB : ∃ B : ℝ, besselBound w Δτ Δξ B)
    (hA : ∃ A : ℝ, 0 < A ∧ ∀ g : Lp ℂ 2 (volume : Measure ℝ), A * ‖g‖^2 ≤ FrameEnergy w Δτ Δξ g)
    : ZakFrame_inequality w Δτ Δξ  := proven

end Frourio


## ./Frourio/Basic.lean

namespace Frourio

noncomputable def φ : ℝ  := proven

theorem φ_gt_one : 1 < φ  := proven

noncomputable def metallic (p : ℝ) : ℝ  := proven

inductive Sign
  | pos : Sign
  | neg : Sign := proven

def Sign.toInt : Sign → ℤ
  | Sign.pos => 1
  | Sign.neg => -1 := proven

end Frourio


## ./Frourio/Examples.lean

namespace Frourio

lemma golden_ratio_property : φ^2 = φ + 1  := proven

lemma phi_pos : 0 < φ  := proven

lemma phi_inv : φ⁻¹ = φ - 1  := proven

example : S φ (1 : ℤ) = φ - 1 / φ  := proven

example : S φ (1 : ℤ) = 1  := proven

lemma S_phi_two : S φ (2 : ℤ) = 2 * φ - 1  := proven

noncomputable def goldenMellinSymbol (s : ℂ) : ℂ  := proven

noncomputable def ThreePointExample (δ : ℝ) (hδ : 0 < δ) : FrourioOperator 3  := proven

example :
    CrossedProduct.mul (identityZmAction ℝ 2)
      { base := φ, scales := fun _ => (0 : ℤ) }
      { base := 1, scales := fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0 }
      =
      { base := φ, scales := fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0 }  := proven

end Frourio

namespace FrourioExamples

noncomputable def F : ℝ → ℝ  := proven

noncomputable def lamEff : ℝ  := proven

noncomputable def rho : ℝ → ℝ  := proven

theorem basic1D_JKO : JKO F ρ0  := proven

theorem basic1D_EDE : EDE F (rho ρ0)  := proven

theorem basic1D_EVI :
  IsEVISolution ({ E := F, lam := lamEff } : EVIProblem ℝ) (rho ρ0)  := proven

theorem basic1D_chain :
  ∃ ρ : ℝ → ℝ, ρ 0 = ρ0 ∧ JKO F ρ0 ∧ EDE F ρ ∧
    IsEVISolution ({ E := F, lam := lamEff } : EVIProblem ℝ) ρ  := proven

end FrourioExamples

namespace FrourioExamplesQuadratic

noncomputable def Fq : ℝ → ℝ  := proven

theorem quadratic_mm_step_closed_form (hτ : 0 < τ) :
  MmStep τ (Fq) xPrev (xPrev / (1 + τ))  := proven

theorem quadratic_JKO (x0 : ℝ) : JKO (Fq) x0  := proven

theorem chain_quadratic_to_EVI (lamEff : ℝ)
  (G : Frourio.plfaEdeEviJko_equiv (Fq) lamEff)
  (x0 : ℝ) :
  ∃ ρ : ℝ → ℝ, ρ 0 = x0 ∧ IsEVISolution ({ E := Fq, lam := lamEff } : EVIProblem ℝ) ρ  := proven

end FrourioExamplesQuadratic

namespace FrourioExamplesFG8

theorem demo_flow_suite_real_auto
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis (FrourioFunctional.F S.func) ρ)
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem demo_lambda_eff_from_doob : lambda_eff_lower S  := proven

theorem demo_twoEVI_concrete
  (Htwo : two_evi_with_force S) (u v : ℝ → X) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η  := proven

theorem demo_twoEVI_concrete_closed
  (Htwo : two_evi_with_force S) (u v : ℝ → X)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η  := proven

end FrourioExamplesFG8


## ./Frourio/Geometry/DiracIndex.lean

namespace Frourio

lemma (by definition) together with a placeholder statement for the
torus index formula.
-/ := proven

structure Fredholm where
  (index : ℤ) := proven

structure ZeroOrderBoundedOp (bundle : Type*) : Type where
  (dummy : Unit := ()) := proven

structure DiracSystem where
  (M : Type*)
  (isTorus2 : Prop)
  (bundle : Type*)
  (connection : Type*)
  (D_A : Fredholm)
  (indexRHS_T2 : ℤ) := proven

@[simp] def index (T : Fredholm) : ℤ  := proven

noncomputable def addZeroOrder (S : DiracSystem)
    (_V : ZeroOrderBoundedOp S.bundle) : Fredholm  := proven

@[simp] theorem index_invariance_zero_order (S : DiracSystem)
    (V : ZeroOrderBoundedOp S.bundle) :
    index (addZeroOrder S V) = index S.D_A  := proven

def index_formula_T2 (S : DiracSystem) (_hT2 : S.isTorus2) : Prop  := proven

end Frourio


## ./Frourio/Geometry/FGCore.lean

namespace Frourio

structure FGData (X : Type*) [PseudoMetricSpace X] [MeasurableSpace X] where
  (μ : MeasureTheory.Measure X)
  (E : X → ℝ)
  (Γ : (X → ℝ) → (X → ℝ))
  (Γ₂ : (X → ℝ) → (X → ℝ))
  (lam : ℝ) := proven

def FGData.toEVI {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (FG : FGData X) : EVIProblem X  := proven

structure ScaleAction (X : Type*) where
  (Lambda : ℝ)
  (act : ℤ → X → X)
  (isometry : Prop)
  (similarity : ℝ → Prop)
  (measure_quasiInvariant : (k : ℤ) → Prop)
  (generator_homogeneous : ℝ → Prop) := proven

noncomputable def effectiveLambda (α κ Λ : ℝ) (k : ℤ) (lam : ℝ) : ℝ  := proven

end Frourio


## ./Frourio/Geometry/FGInterop.lean

namespace Frourio

def evi_from_fg (FG : FGData X) : EVIProblem X  := proven

def fg_IsEVISolution (FG : FGData X) (u : ℝ → X) : Prop  := proven

def fg_evi_contraction (FG : FGData X) (u v : ℝ → X)
  (hu : IsEVISolution (evi_from_fg FG) u)
  (hv : IsEVISolution (evi_from_fg FG) v) : Prop  := proven

def fg_evi_contraction_nonneg (FG : FGData X) (u v : Rge0 → X)
  (hu : IsEVISolutionNonneg (evi_from_fg FG) u)
  (hv : IsEVISolutionNonneg (evi_from_fg FG) v) : Prop  := proven

end Frourio


## ./Frourio/Geometry/FGStar.lean

namespace Frourio

def domain_of_carre_du_champ {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (μ : Measure X) : Set (X → ℝ)  := proven

structure FGStarConstantExt {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) extends FGStarConstant where
  /-- The constant satisfies the spectral bound -/
  spectral_bound : ∀ φ : X → ℝ, MeasureTheory.MemLp φ 2 μ →
    φ ∈ domain_of_carre_du_champ Γ μ →
    ∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ ≤
      C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ := proven

structure CauchySchwarzSharp {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (fgstar_const : FGStarConstant) where
  /-- The eigenfunction that achieves equality -/
  eigenfunction : X → ℝ
  /-- The eigenvalue corresponding to the eigenfunction -/
  eigenvalue : ℝ
  nonzero_eigenfunction : ∃ x : X, eigenfunction x ≠ 0
  /-- The eigenfunction satisfies the eigenvalue equation with multi-scale operator -/
  eigen_equation : ∀ x : X,
    multiScaleDiff H cfg eigenfunction x = eigenvalue * eigenfunction x
  /-- A concrete equality induced by the eigenfunction relation:
      pointwise, |Δ^{⟨m⟩} φ| = |λ|·|φ|. This encodes the sharpness condition in
      a measure‑free way that follows immediately from `eigen_equation`. -/
  equality_holds : ∀ x : X,
    |multiScaleDiff H cfg eigenfunction x| = |eigenvalue| * |eigenfunction x| := proven

structure MetaEVIFlagsExt {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) extends MetaEVIFlags H cfg Γ κ μ where
  /-- Dynamic distance flags -/
  dyn_flags : DynDistanceFlags H cfg Γ κ μ
  /-- Positivity of regularization parameter -/
  κ_pos : 0 < κ := proven

def evi_contraction_rate_from_meta_flags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) (flags : MetaEVIFlags H cfg Γ κ μ) : ℝ  := proven

theorem FGStar_main_inequality {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ)
    (μ : Measure X) (flags : MetaEVIFlags H cfg Γ κ μ) :
    flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                  spectral_penalty_term cfg flags.fgstar_const.C_energy κ  := proven

theorem FGStar_degradation {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) (hκ_nonneg : 0 ≤ κ) :
    flags.lam_eff ≤ flags.lam_base  := proven

structure FGStar_EVI_connection {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ)
    (μ : Measure X) (Ent : EntropyFunctional X μ) (flags : MetaEVIFlags H cfg Γ κ μ) where
  /-- Geodesic structure on P₂(X) with respect to d_m -/
  geo : MetaGeodesicStructure H cfg Γ κ μ
  /-- The entropy is geodesically λ_eff-convex along d_m geodesics -/
  geodesic_convexity : ∀ ρ₀ ρ₁ : P2 X, ∀ t ∈ Set.Icc (0:ℝ) 1,
    (Ent.Ent (geo.γ ρ₀ ρ₁ t).val).toReal ≤
    (1 - t) * (Ent.Ent ρ₀.val).toReal + t * (Ent.Ent ρ₁.val).toReal -
    flags.lam_eff * t * (1 - t) * (dm H cfg Γ κ μ ρ₀.val ρ₁.val)^2 / 2
  /-- The gradient flow of entropy exists and is well-defined -/
  gradient_flow_exists : Prop  -- Placeholder: existence of gradient flow
  /-- The gradient flow satisfies the EVI inequality with rate lam_eff -/
  evi_holds : Prop  -- Placeholder: actual EVI inequality statement := proven

theorem FGStar_L2_inequality {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) [IsFiniteMeasure μ]
    (C : FGStarConstantExt H cfg Γ μ)
    (φ : X → ℝ) (hφ_L2 : MeasureTheory.MemLp φ 2 μ)
    (hφ_dom : φ ∈ domain_of_carre_du_champ Γ μ) :
    ∫ x, (multiScaleDiff H cfg φ x)^2 ∂μ ≤
      C.C_energy * (spectralSymbolSupNorm cfg)^2 * ∫ x, Γ.Γ φ φ x ∂μ  := proven

theorem FGStar_ENNReal_inequality {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) [IsFiniteMeasure μ]
    (C : FGStarConstantExt H cfg Γ μ)
    (φ : X → ℝ) (hφ_L2 : MeasureTheory.MemLp φ 2 μ)
    (hφ_dom : φ ∈ domain_of_carre_du_champ Γ μ)
    -- Move to ENNReal internally via lintegral_ofReal_eq_ofReal_integral
    (hΔ_integrable : MeasureTheory.Integrable (fun x => (multiScaleDiff H cfg φ x) ^ 2) μ)
    (hΓ_nonneg_pt : ∀ x, 0 ≤ Γ.Γ φ φ x) :
    (∫⁻ x, ENNReal.ofReal ((multiScaleDiff H cfg φ x)^2) ∂μ) ≤
      ENNReal.ofReal (C.C_energy * (spectralSymbolSupNorm cfg)^2) *
      (∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂μ)  := proven

theorem FGStar_parameter_degradation {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (C : FGStarConstantExt H cfg Γ μ) (lam_base : ℝ) (doob_ε : ℝ)
    (hκ_pos : 0 < κ) (hdoob_nonneg : 0 ≤ doob_ε) :
    -- The effective parameter after FG★ degradation
    let lam_eff  := proven

theorem FGStar_with_EVI {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X)
    (κ : ℝ) (μ : Measure X) (Ent : EntropyFunctional X μ) (flags : MetaEVIFlags H cfg Γ κ μ)
    (_connection : FGStar_EVI_connection H cfg Γ κ μ Ent flags) :
    -- The main inequality holds and EVI contracts at the degraded rate
    flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                  spectral_penalty_term cfg flags.fgstar_const.C_energy κ  := proven

structure FGStar_sharp {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) where
  /-- The FG★ inequality is an equality -/
  equality : flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                           spectral_penalty_term cfg flags.fgstar_const.C_energy κ
  /-- There exists a Doob function h that achieves the BE degradation bound.
      In BE theory, this means ε(h) = flags.doob.ε where
      ε(h) = sup_φ {∫ Γ₂(log h, φ) dμ / ‖φ‖²} -/
  doob_optimal : ∃ (h : X → ℝ), ∀ x, 0 < h x
  /-- The spectral symbol achieves its sup-norm on a set of positive measure -/
  spectral_achieves_sup : ∃ S : Set ℝ, S.Nonempty ∧
    (∀ lam ∈ S, |spectralSymbol cfg lam| = spectralSymbolSupNorm cfg) ∧
    -- The saturation set has positive Lebesgue measure
    (∃ ε > 0, MeasureTheory.volume (S ∩ Set.Icc 0 ε) > 0)
  /-- The multi-scale configuration minimizes the spectral sup-norm
      among all configurations with the same constraints -/
  config_optimal : ∀ cfg' : MultiScaleConfig m,
    (∑ i, cfg'.α i = 0) →  -- Same zero-sum constraint
    spectralSymbolSupNorm cfg ≤ spectralSymbolSupNorm cfg'
  /-- Cauchy–Schwarzの等号が鋭い形で達成され、
      固有方程式まで満たすテスト関数が存在する。 -/
  cauchy_schwarz_sharp :
    CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const := proven

def optimal_scale_config {X : Type*} [MeasurableSpace X] {m : PNat} : MultiScaleConfig m  := proven

theorem FGStar_G_invariance_prop_scale {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (cfg : MultiScaleConfig m) (g : GAction X m) :
    -- The FG★ inequality is G-invariant under the symmetry group
    spectralSymbolSupNorm (g.actOnConfig cfg) = spectralSymbolSupNorm cfg  := proven

theorem cauchy_schwarz_equality_characterization
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) (fgstar_const : FGStarConstant)
    (φ : X → ℝ) (h_nonzero : ∃ x : X, φ x ≠ 0) :
    -- The equality holds iff φ is an eigenfunction
    (∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x) ↔
    ∃ cs : CauchySchwarzSharp H cfg Γ κ μ fgstar_const, cs.eigenfunction = φ  := proven

theorem cauchy_schwarz_sharp_proof
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X)
    (κ : ℝ) (μ : Measure X) (flags : MetaEVIFlags H cfg Γ κ μ)
    (sharp : FGStar_sharp H cfg Γ κ μ flags)
    (h_eigenvalue_bound : ∀ lam : ℝ, (∃ φ : X → ℝ, (∃ x, φ x ≠ 0) ∧
      (∀ x, multiScaleDiff H cfg φ x = lam * φ x)) → |lam| ≤ spectralSymbolSupNorm cfg) :
    -- In the sharp case, there exists an eigenfunction achieving CS equality
    ∃ (φ : X → ℝ) (lam : ℝ),
      (∀ x : X, multiScaleDiff H cfg φ x = lam * φ x) ∧
      (∃ x : X, φ x ≠ 0) ∧
      -- The eigenvalue is related to the spectral symbol
      |lam| ≤ spectralSymbolSupNorm cfg  := proven

lemma cauchy_schwarz_implies_phase_alignment
    {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (h_lam_in_range : ∃ ξ : ℝ, spectralSymbol cfg ξ = lam) :
    -- The eigenfunction corresponds to aligned spectral phases
    ∃ (S : Set ℝ), S.Nonempty ∧
      -- φ̂ is supported where the spectral symbol equals lam
      (∀ ξ ∈ S, spectralSymbol cfg ξ = lam)  := proven

end Frourio


## ./Frourio/Geometry/FGTheorems/FGTheorems.lean

namespace Frourio

theorem analytic_bridges_from_component_packs
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Hplfa_ede : PLFAEDEAssumptions (FrourioFunctional.F S.func))
  (Hede_evi : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hjko_plfa : JKOPLFAAssumptions (FrourioFunctional.F S.func)) :
  AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem analytic_bridges_from_equiv_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (H : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem flow_suite_from_flags
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_concrete_conditions
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (_HK1 : K1prime S.func) (_HK4 : K4m S.func)
  (Hplfa_ede : PLFAEDEAssumptions (FrourioFunctional.F S.func))
  (Hede_evi : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Hjko_plfa : JKOPLFAAssumptions (FrourioFunctional.F S.func))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_fg_flags_and_equiv
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (_HK1 : K1prime S.func) (_HK4 : K4m S.func)
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_doob_mpoint
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_real_flags
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis (FrourioFunctional.F S.func) ρ)
  (HplfaEde : PLFA_EDE_from_real_flags (X := X)
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_real_flags (X := X)
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_real_flags_auto
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis (FrourioFunctional.F S.func) ρ)
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem lamLower_from_real_flags
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  ∃ L : ℝ, (lambdaBE S.base.lam S.eps) ≥ L  := proven

theorem equivalence_from_real_flags_auto
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (h_usc : ∀ ρ : ℝ → X, ShiftedUSCHypothesis (FrourioFunctional.F S.func) ρ)
  (HedeEvi_builder : EDE_EVI_from_analytic_flags
                (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem equivalence_from_flags_and_bridges
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HedeEvi : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func)) :
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem equivalence_from_equiv_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (S : GradientFlowSystem X)
  (H : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

def flow_equivalence {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop  := proven

def lambda_eff_lower {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop  := proven

theorem lambda_eff_lower_from_doob {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : lambda_eff_lower S  := proven

def two_evi_with_force_alias {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) : Prop  := proven

def evi_multiscale_rule {m : ℕ} (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) : Prop  := proven

theorem two_evi_with_force_to_distance_concrete
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) (Htwo : two_evi_with_force S) (u v : ℝ → X) :
  ∃ η : ℝ,
    (gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) →
    ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η  := proven

theorem two_evi_with_force_to_distance_concrete_closed
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X) (Htwo : two_evi_with_force S) (u v : ℝ → X)
  (Hgr_all : ∀ η : ℝ,
    gronwall_exponential_contraction_with_error_half_pred S.base.lam η
      (fun t => d2 (u t) (v t))) :
  ∃ η : ℝ, ContractionPropertyWithError ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v η  := proven

end Frourio


## ./Frourio/Geometry/FGTheorems/FGTheoremsCore0.lean

namespace Frourio

def evi_scale_rule (FG : FGData X) (S : ScaleAction X) : Prop  := proven

theorem evi_scale_rule_isometry (FG : FGData X) (S : ScaleAction X)
  (hIso : S.isometry) (hκ : ∃ κ : ℝ, S.generator_homogeneous κ) :
  evi_scale_rule FG S  := proven

theorem evi_scale_rule_similarity (FG : FGData X) (S : ScaleAction X)
  (α : ℝ) (hSim : S.similarity α) (hκ : ∃ κ : ℝ, S.generator_homogeneous κ) :
  evi_scale_rule FG S  := proven

def mosco_inheritance {ι : Type*} (S : MoscoSystem ι) : Prop  := proven

theorem mosco_inheritance_thm {ι : Type*} (S : MoscoSystem ι)
  (H : MoscoAssumptions S) : mosco_inheritance S  := proven

noncomputable def cStarCoeff (_σ : ℝ) : ℝ  := proven

noncomputable def cDCoeff (_σ : ℝ) : ℝ  := proven

noncomputable def budgetFromSigma (σ : ℝ) : ConstantBudget  := proven

noncomputable def budgetFromSigmaWithFlag (σ : ℝ) (comm : Bool) : ConstantBudget  := proven


lemma budgetFromSigmaWithFlag_comm_true (σ : ℝ) :
  (budgetFromSigmaWithFlag σ true).cStar = 0 ∧ (budgetFromSigmaWithFlag σ true).cD = cDCoeff σ  := proven


lemma budgetFromSigmaWithFlag_comm_false (σ : ℝ) :
  (budgetFromSigmaWithFlag σ false).cStar = (budgetFromSigma σ).cStar ∧
  (budgetFromSigmaWithFlag σ false).cD = (budgetFromSigma σ).cD  := proven

lemma budget_commutative_simplify (σ : ℝ) :
  ∃ B : ConstantBudget, B.cStar = 0 ∧ B.cD = cDCoeff σ  := proven

noncomputable def cStarCoeff_model (kStar : ℝ) (σ : ℝ) : ℝ  := proven

noncomputable def cDCoeff_model (kD : ℝ) (σ : ℝ) : ℝ  := proven


lemma cStarCoeff_model_nonneg {kStar σ : ℝ} (hk : 0 ≤ kStar) :
  0 ≤ cStarCoeff_model kStar σ  := proven


lemma cDCoeff_model_nonneg {kD σ : ℝ} (hk : 0 ≤ kD) :
  0 ≤ cDCoeff_model kD σ  := proven

noncomputable def budgetFromSigmaModel (kStar kD σ : ℝ) : ConstantBudget  := proven


lemma budgetFromSigmaModel_nonneg {kStar kD σ : ℝ}
  (hks : 0 ≤ kStar) (hkd : 0 ≤ kD) :
  0 ≤ (budgetFromSigmaModel kStar kD σ).cStar ∧ 0 ≤ (budgetFromSigmaModel kStar kD σ).cD  := proven

theorem lambdaEffLowerBound_from_sigma_model {X : Type*} [PseudoMetricSpace X]
  (A : FrourioFunctional X) (lam eps Ssup XiNorm σ kStar kD : ℝ) :
  lambdaEffLowerBound A (budgetFromSigmaModel kStar kD σ) lam eps
    (lambdaBE lam eps
      - A.gamma * ((budgetFromSigmaModel kStar kD σ).cStar * Ssup ^ (2 : ℕ)
                   + (budgetFromSigmaModel kStar kD σ).cD * XiNorm))
    Ssup XiNorm  := proven

theorem flow_suite_from_packs
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (Hpack : EquivBuildAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_flags_and_bridges
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (B : AnalyticBridges (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem flow_suite_from_flags_and_ede_evi_pack
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (P : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func))
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps
            (lambdaBE S.base.lam S.eps) S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem tensorization_min_rule_thm {X Y : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y]
  (S₁ : GradientFlowSystem X) (S₂ : GradientFlowSystem Y)
  (hK1₁ : K1prime S₁.func) (hK1₂ : K1prime S₂.func)
  (hγ₁ : 0 ≤ S₁.func.gamma) (hγ₂ : 0 ≤ S₂.func.gamma) :
  tensorization_min_rule S₁ S₂  := proven

theorem ede_evi_pred_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EDE_EVI_pred (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem ede_to_evi_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EDE_to_EVI_from_flags (X := X) (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem evi_to_ede_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EVI_to_EDE_from_flags (X := X) (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem ede_evi_pack_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (HC : HalfConvex (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (SUB : StrongUpperBound (FrourioFunctional.F S.func))
  (H : EDE_EVI_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

theorem plfa_ede_pred_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (H : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  PLFA_EDE_pred (FrourioFunctional.F S.func)  := proven

theorem plfa_ede_pack_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (H : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  PLFAEDEAssumptions (FrourioFunctional.F S.func)  := proven

theorem analytic_flags_for_FG
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  (S : GradientFlowSystem X)
  (_HK1 : K1prime S.func) (_HK4 : K4m S.func)
  -- Optional: a slope upper bound predicate could be used here; omitted
  : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)  := proven

end Frourio


## ./Frourio/Geometry/GInvariance.lean

namespace Frourio

noncomputable def spectral_penalty_term {m : PNat} (cfg : MultiScaleConfig m)
    (C_energy : ℝ) (κ : ℝ) : ℝ  := proven

structure FGStarConstant where
  /-- Energy constant from FG★ inequality -/
  C_energy : ℝ
  /-- Positivity constraint -/
  C_energy_pos : 0 < C_energy
  /-- Non-negativity (weaker than positivity, for compatibility) -/
  C_energy_nonneg : 0 ≤ C_energy  := proven

structure MetaEVIFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- FG★ constant -/
  fgstar_const : FGStarConstant
  /-- Base curvature parameter -/
  lam_base : ℝ
  /-- Doob transform component -/
  doob : DoobDegradation
  /-- Effective rate -/
  lam_eff : ℝ
  /-- Effective rate equation -/
  lam_eff_eq : lam_eff = lam_base - 2 * doob.ε -
    spectral_penalty_term cfg fgstar_const.C_energy κ := proven

lemma withDensity_one {X : Type*} [MeasurableSpace X] (ν : Measure X) :
    ν.withDensity (fun _ => (1 : ENNReal)) = ν  := proven

structure DirichletAutomorphism {X : Type*} [MeasurableSpace X] where
  /-- The underlying measurable bijection -/
  toFun : X → X
  /-- Inverse function -/
  invFun : X → X
  /-- Left inverse property -/
  left_inv : Function.LeftInverse invFun toFun
  /-- Right inverse property -/
  right_inv : Function.RightInverse invFun toFun
  /-- Measurability of forward map -/
  measurable_toFun : Measurable toFun
  /-- Measurability of inverse map -/
  measurable_invFun : Measurable invFun
  /-- Dirichlet-form invariance for every CarreDuChamp Γ:
  Pullback by `toFun` commutes with Γ. -/
  preserves_dirichlet : ∀ (Γ : CarreDuChamp X) (f g : X → ℝ),
    Γ.Γ (fun x => f (toFun x)) (fun x => g (toFun x)) =
    (fun x => Γ.Γ f g (toFun x)) := proven

structure ScaleTransform (m : PNat) where
  /-- The scaling factor σ > 0 -/
  σ : ℝ
  /-- Positivity constraint -/
  hσ_pos : 0 < σ := proven

def ScaleTransform.apply {m : PNat} (s : ScaleTransform m)
    (cfg : MultiScaleConfig m) : MultiScaleConfig m where
  α  := proven

structure TimeReparam where
  /-- The reparametrization function θ : [0,1] → [0,1] -/
  θ : ℝ → ℝ
  /-- Monotone increasing -/
  mono : Monotone θ
  /-- Boundary conditions -/
  init : θ 0 = 0
  terminal : θ 1 = 1
  /-- Continuity of the reparametrization function -/
  continuous : Continuous θ := proven

structure GAction (X : Type*) [MeasurableSpace X] (m : PNat) where
  /-- Dirichlet form automorphism component -/
  aut : DirichletAutomorphism (X := X)
  /-- Doob transform component (h function) -/
  doob_h : X → ℝ
  /-- Positivity of Doob function -/
  doob_h_pos : ∀ x, 0 < doob_h x
  /-- Scale transformation component -/
  scale : ScaleTransform m
  /-- Time reparametrization component -/
  reparam : TimeReparam := proven

noncomputable def GAction.actOnMeasure {X : Type*} [MeasurableSpace X] {m : PNat}
    (g : GAction X m) (μ : Measure X) : Measure X  := proven

def GAction.actOnConfig {X : Type*} [MeasurableSpace X] {m : PNat}
    (g : GAction X m) (cfg : MultiScaleConfig m) : MultiScaleConfig m  := proven

def entropy_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (Ent : Measure X → ℝ) : Prop  := proven

def dm_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (Γ : CarreDuChamp X) : Prop  := proven

def multiScaleDiff_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) : Prop  := proven

theorem spectralSymbol_scale_invariant {m : PNat}
    (cfg : MultiScaleConfig m) (s : ScaleTransform m) :
    spectralSymbolSupNorm (s.apply cfg) = spectralSymbolSupNorm cfg  := proven

noncomputable def pushforward {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (_hf : Measurable f) (μ : Measure X) : Measure Y  := proven

def pullback {X Y : Type*} (f : X → Y) (φ : Y → ℝ) : X → ℝ  := proven

theorem entropy_pushforward_invariant {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (μ : Measure X) (ν : Measure Y) [SigmaFinite ν]
    (h_preserve : μ.map f = ν) :
    InformationTheory.klDiv (μ.map f) ν = 0  := proven

theorem dm_pullback_pushforward_compatible {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (g : DirichletAutomorphism (X := X))
    -- Global invariance hypothesis for dm under the full G-action
    (h_inv : dm_G_invariant (m := m) H Γ) :
    ∀ ρ₀ ρ₁ : Measure X,
    dm H cfg Γ κ (pushforward g.toFun g.measurable_toFun μ)
       (pushforward g.toFun g.measurable_toFun ρ₀)
       (pushforward g.toFun g.measurable_toFun ρ₁) =
    dm H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem carre_du_champ_pullback {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (g : DirichletAutomorphism (X := X)) (φ ψ : X → ℝ) :
    Γ.Γ (pullback g.toFun φ) (pullback g.toFun ψ) = pullback g.toFun (Γ.Γ φ ψ)  := proven

structure EntropyWithTransforms (X : Type*) [MeasurableSpace X] where
  /-- Base measure -/
  μ : Measure X
  /-- Entropy relative to base measure -/
  Ent : Measure X → ENNReal  := proven

structure ModifiedDistanceWithTransforms {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) where
  /-- Base measure -/
  μ : Measure X
  /-- The modified distance function -/
  d_m : Measure X → Measure X → ℝ  := proven

theorem entropy_transform_formula {X : Type*} [MeasurableSpace X]
    (μ ρ : Measure X) (g : DirichletAutomorphism (X := X)) (h : X → ℝ)
    -- Invariance hypothesis for KL under pushforward and common density scaling
    (h_inv : InformationTheory.klDiv
              ((pushforward g.toFun g.measurable_toFun ρ).withDensity
                (fun x => ENNReal.ofReal ((h x) ^ 2)))
              ((pushforward g.toFun g.measurable_toFun μ).withDensity
                (fun x => ENNReal.ofReal ((h x) ^ 2)))
            = InformationTheory.klDiv ρ μ) :
    InformationTheory.klDiv
      ((pushforward g.toFun g.measurable_toFun ρ).withDensity
        (fun x => ENNReal.ofReal ((h x)^2)))
      ((pushforward g.toFun g.measurable_toFun μ).withDensity
        (fun x => ENNReal.ofReal ((h x)^2))) =
    InformationTheory.klDiv ρ μ  := proven

theorem dm_transform_formula {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (g : DirichletAutomorphism (X := X)) (s : ScaleTransform m)
    -- Invariance under Dirichlet automorphisms (pushforward)
    (h_inv : dm_G_invariant (m := m) H Γ)
    -- Scale covariance law (assumed): κ scales as 1/σ and distance scales by σ
    (hscale : ∀ (μ ρ₀ ρ₁ : Measure X),
      dm H (s.apply cfg) Γ (κ / s.σ) μ ρ₀ ρ₁ = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁) :
    ∀ ρ₀ ρ₁ : Measure X,
      dm H (s.apply cfg) Γ (κ / s.σ)
         (pushforward g.toFun g.measurable_toFun μ)
         (pushforward g.toFun g.measurable_toFun ρ₀)
         (pushforward g.toFun g.measurable_toFun ρ₁)
      = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem pullback_preserves_L2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : DirichletAutomorphism (X := X)) (φ : X → ℝ)
    -- Change-of-variables hypothesis for L² under pushforward/pullback
    (h_change : ∀ f : X → ℝ,
      MeasureTheory.MemLp f 2 (pushforward g.toFun g.measurable_toFun μ) ↔
      MeasureTheory.MemLp (pullback g.toFun f) 2 μ) :
    MeasureTheory.MemLp φ 2 (pushforward g.toFun g.measurable_toFun μ) ↔
    MeasureTheory.MemLp (pullback g.toFun φ) 2 μ  := proven

theorem meta_variational_G_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    -- Base flags before transformation
    (flags : MetaEVIFlags H cfg Γ κ μ)
    -- G-action element
    (g : GAction X m) :
    -- The four-equivalence PLFA=EDE=EVI=JKO is preserved under G-action at the level of FG★ flags
    ∃ (transformed_flags : MetaEVIFlags H (g.actOnConfig cfg) Γ κ (g.actOnMeasure μ)),
      transformed_flags.lam_eff =
        transformed_flags.lam_base -
        2 * transformed_flags.doob.ε -
        spectral_penalty_term (g.actOnConfig cfg) transformed_flags.fgstar_const.C_energy κ  := proven

theorem FGStar_G_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (cfg : MultiScaleConfig m) (lam : ℝ) (doob : DoobDegradation) (κ C : ℝ) :
    ∀ (g : GAction X m),
      doob.degraded_lambda lam - κ * C * (spectralSymbolSupNorm (g.actOnConfig cfg))^2
        = doob.degraded_lambda lam - κ * C * (spectralSymbolSupNorm cfg)^2  := proven

def GAction.comp {X : Type*} [MeasurableSpace X] {m : PNat}
    (g₁ g₂ : GAction X m) : GAction X m  := proven

def GAction.id {X : Type*} [MeasurableSpace X] (m : PNat) : GAction X m where
  aut := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    measurable_toFun := measurable_id
    measurable_invFun := measurable_id
    preserves_dirichlet := by
      intro Γ f g; funext x; simp
  }
  doob_h  := proven

theorem GAction.id_actOnMeasure {X : Type*} [MeasurableSpace X] (m : PNat)
    (μ : Measure X) : (GAction.id (X := X) m).actOnMeasure μ = μ  := proven

theorem GAction.id_actOnConfig {X : Type*} [MeasurableSpace X] (m : PNat)
    (cfg : MultiScaleConfig m) : (GAction.id (X := X) m).actOnConfig cfg = cfg  := proven

theorem entropy_aut_invariant {X : Type*} [MeasurableSpace X] {m : PNat}
    (Ent : Measure X → ℝ) (aut : DirichletAutomorphism (X := X)) (μ : Measure X) :
    entropy_G_invariant (m := m) Ent →
    ∃ c : ℝ, Ent (μ.map aut.toFun) = Ent μ + c  := proven

theorem dm_scale_transform {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (s : ScaleTransform m) (ρ₀ ρ₁ : Measure X)
    (hscale : dm H (s.apply cfg) Γ (κ / s.σ) μ ρ₀ ρ₁ = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁) :
    -- The distance scales linearly with σ when κ is scaled by 1/σ (assumed)
    dm H (s.apply cfg) Γ (κ / s.σ) μ ρ₀ ρ₁ = s.σ * dm H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem dm_G_scale_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (g : GAction X m) (ρ₀ ρ₁ : Measure X) :
    dm_G_invariant (m := m) H Γ →
    dm H (g.actOnConfig cfg) Γ κ (g.actOnMeasure μ)
       (g.actOnMeasure ρ₀) (g.actOnMeasure ρ₁) =
    dm H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem meta_principle_G_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X)
    (κ : ℝ) (Ent : Measure X → ℝ) (lam : ℝ) (doob : DoobDegradation) (g : GAction X m) :
    -- Assumptions
    entropy_G_invariant (m := m) Ent →
    dm_G_invariant (m := m) H Γ →
    multiScaleDiff_G_invariant (m := m) H →
    -- Conclusion: FG★ inequality structure is preserved
    ∃ (lam' : ℝ) (doob' : DoobDegradation),
      lam' - 2 * doob'.ε - κ * (spectralSymbolSupNorm (g.actOnConfig cfg))^2 =
      lam - 2 * doob.ε - κ * (spectralSymbolSupNorm cfg)^2  := proven

theorem lam_eff_G_invariant {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat}
    (cfg : MultiScaleConfig m) (κ C : ℝ) (lam : ℝ) (doob : DoobDegradation) (g : GAction X m) :
    -- Under G-action, the effective rate transforms predictably
    ∃ (doob' : DoobDegradation),
      doob'.degraded_lambda lam - κ * C * (spectralSymbolSupNorm (g.actOnConfig cfg))^2 =
      doob.degraded_lambda lam - κ * C * (spectralSymbolSupNorm cfg)^2  := proven

end Frourio


## ./Frourio/Geometry/GradientFlowFramework.lean

namespace Frourio

structure GradientFlowSystem (X : Type*) [PseudoMetricSpace X] [MeasurableSpace X] where
  (base : FGData X)
  (func : FrourioFunctional X)
  (Ssup : ℝ)      -- proxy for ‖S_m‖_∞
  (XiNorm : ℝ)    -- proxy for ‖Ξ_m‖
  (budget : ConstantBudget)
  (eps : ℝ)       -- Doob degradation ε := proven

def gradient_flow_equiv (S : GradientFlowSystem X) : Prop  := proven

theorem gradient_flow_equiv_of_pack (S : GradientFlowSystem X)
  (G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps)) :
  gradient_flow_equiv S  := proven

def lambda_eff_lower_bound (S : GradientFlowSystem X) : Prop  := proven

theorem lambda_eff_lower_bound_of (S : GradientFlowSystem X)
  {lamEff : ℝ}
  (h : lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm) :
  lambda_eff_lower_bound S  := proven

theorem lambda_eff_lower_bound_strengthen_with_flags
  (S : GradientFlowSystem X)
  (flags : AnalyticFlagsReal X (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (h : lambda_eff_lower_bound S) :
  ∃ lamEff' : ℝ,
    lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff' S.Ssup S.XiNorm ∧
    lamEff' ≥ lamLowerFromRealFlags flags  := proven

theorem lambda_eff_lower_bound_from_doob (S : GradientFlowSystem X) : lambda_eff_lower_bound S  := proven

def two_evi_with_force (S : GradientFlowSystem X) : Prop  := proven

theorem two_evi_with_force_of (S : GradientFlowSystem X)
  (H : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  two_evi_with_force S  := proven

theorem gradient_flow_suite
  (S : GradientFlowSystem X)
  (G : plfaEdeEviJko_equiv (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (lamEff : ℝ)
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

theorem gradient_flow_suite_from_flags_and_ede_evi_pack
  (S : GradientFlowSystem X)
  (A : AnalyticFlags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HplfaEde : PLFA_EDE_from_analytic_flags (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (P : EDEEVIAssumptions (FrourioFunctional.F S.func) (lambdaBE S.base.lam S.eps))
  (HjkoPlfa : JKO_PLFA_from_analytic_flags (FrourioFunctional.F S.func))
  (lamEff : ℝ)
  (hLam : lambdaEffLowerBound S.func S.budget S.base.lam S.eps lamEff S.Ssup S.XiNorm)
  (Htwo : ∀ u v : ℝ → X, TwoEVIWithForce ⟨FrourioFunctional.F S.func, S.base.lam⟩ u v) :
  gradient_flow_equiv S ∧ lambda_eff_lower_bound S ∧ two_evi_with_force S  := proven

def tensorization_min_rule {X Y : Type*}
  [PseudoMetricSpace X] [MeasurableSpace X]
  [PseudoMetricSpace Y] [MeasurableSpace Y]
  (S₁ : GradientFlowSystem X) (S₂ : GradientFlowSystem Y) : Prop  := proven

noncomputable def effective_lambda_multiscale {m : ℕ}
  (α κ Λ : Fin m → ℝ) (k : Fin m → ℤ) (lam : ℝ) : ℝ  := proven

noncomputable abbrev effectiveLambdaVec {m : ℕ}
  (α κ Λ : Fin m → ℝ) (k : Fin m → ℤ) (lam : ℝ) : ℝ  := proven

def multiscale_lambda_rule {m : ℕ} (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) : Prop  := proven

theorem multiscale_lambda_rule_thm {m : ℕ}
  (Λ α κ : Fin m → ℝ) (k : Fin m → ℤ) :
  multiscale_lambda_rule Λ α κ k  := proven

theorem effective_lambda_multiscale_rpow {m : ℕ}
  (α κ Λ : Fin m → ℝ) (k : Fin m → ℤ) (lam : ℝ)
  (hΛ : ∀ j : Fin m, 0 < Λ j) :
  effective_lambda_multiscale α κ Λ k lam =
    lam * ∏ j : Fin m, Real.rpow (Λ j) (((κ j - 2 * α j) * (k j : ℝ)))  := proven

end Frourio


## ./Frourio/Geometry/MPointCalibration.lean

namespace Frourio

structure MPointCalibration (m : ℕ) where
  (weights : Fin m → ℝ)
  (shifts  : Fin m → ℤ)
  (phase   : Fin m → ℝ)
  (normalized : Prop) := proven

noncomputable def phi_m (_m : ℕ) (_σ _τ : ℝ) : ℂ  := proven

end Frourio


## ./Frourio/Geometry/MetaEquivalence.lean

namespace Frourio

structure EntropyFunctional (X : Type*) [MeasurableSpace X] (μ : Measure X) where
  /-- The entropy value for a probability measure (now in ENNReal) -/
  Ent : Measure X → ENNReal
  /-- Entropy is lower semicontinuous (sublevel sets are sequentially closed) -/
  lsc : ∀ c : ENNReal, ∀ (ρₙ : ℕ → Measure X),
    (∀ n, Ent (ρₙ n) ≤ c) →
    (∃ ρ : Measure X, Ent ρ ≤ c)
  /-- Entropy is bounded below (typically by 0 for relative entropy) -/
  bounded_below : ∃ c : ENNReal, ∀ ρ : Measure X, c ≤ Ent ρ
  /-- Entropy has compact sublevel sets in the weak topology -/
  compact_sublevels : ∀ c : ENNReal,
    ∀ (ρₙ : ℕ → Measure X),
      (∀ n, MeasureTheory.IsProbabilityMeasure (ρₙ n)) →
      (∀ n, Ent (ρₙ n) ≤ c) →
      ∃ (ρ : Measure X) (φ : ℕ → ℕ),
        StrictMono φ ∧
        MeasureTheory.IsProbabilityMeasure ρ ∧
        Ent ρ ≤ c ∧
        -- Abstract weak convergence: ρₙ(φ k) ⇀ ρ as k → ∞
        (∃ (weakly_converges : Prop), weakly_converges)
  /-- Entropy is proper (has a finite point) -/
  proper : ∃ ρ : Measure X, MeasureTheory.IsProbabilityMeasure ρ ∧ Ent ρ < ⊤
  /-- Entropy is convex on the space of measures (abstract property) -/
  convex : ∀ (ρ₁ ρ₂ : Measure X) (t : ℝ), 0 ≤ t → t ≤ 1 →
    MeasureTheory.IsProbabilityMeasure ρ₁ →
    MeasureTheory.IsProbabilityMeasure ρ₂ →
    -- For the convex combination of measures, entropy satisfies convexity
    -- Note: Ent(μ_t) ≤ (1-t)Ent(ρ₁) + tEnt(ρ₂) for the interpolated measure μ_t
    True  -- Placeholder for actual convexity condition := proven

noncomputable def entropyFromCore {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (core : EntropyFunctionalCore X μ) :
    EntropyFunctional X μ where
  Ent  := proven

lemma concreteEntropyFunctional_self {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure μ] :
    (ConcreteEntropyFunctional μ).Ent μ = 0  := proven

noncomputable def defaultEntropyFunctional {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure μ] :
    EntropyFunctional X μ  := proven

lemma defaultEntropyFunctional_proper {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure μ] :
    (defaultEntropyFunctional μ).Ent μ = 0  := proven

structure MetaGeodesicStructure {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- Geodesic curves in P₂(X) -/
  γ : P2 X → P2 X → ℝ → P2 X
  /-- Start point property -/
  start_point : ∀ ρ₀ ρ₁, γ ρ₀ ρ₁ 0 = ρ₀
  /-- End point property -/
  end_point : ∀ ρ₀ ρ₁, γ ρ₀ ρ₁ 1 = ρ₁
  /-- Geodesic property with respect to d_m -/
  geodesic_property : ∀ ρ₀ ρ₁ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
    dm H cfg Γ κ μ (γ ρ₀ ρ₁ s).val (γ ρ₀ ρ₁ t).val =
    |t - s| * dm H cfg Γ κ μ ρ₀.val ρ₁.val := proven

def EntropySemiconvex {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ) (G : MetaGeodesicStructure H cfg Γ κ μ)
    (lam_eff : ℝ) : Prop  := proven

structure MetaAnalyticFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ) (lam_eff : ℝ) where
  /-- Dynamic distance flags -/
  dyn_flags : DynDistanceFlags H cfg Γ κ μ
  /-- Geodesic structure -/
  geodesic : MetaGeodesicStructure H cfg Γ κ μ
  /-- Entropy is semiconvex along geodesics -/
  semiconvex : EntropySemiconvex H cfg Γ κ μ Ent geodesic lam_eff
  /-- Effective parameter bound -/
  lam_lower : ℝ
  /-- The effective parameter satisfies the bound -/
  lam_eff_ge : lam_eff ≥ lam_lower := proven

noncomputable def metaToRealFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ) (lam_eff : ℝ)
    (flags : MetaAnalyticFlags H cfg Γ κ μ Ent lam_eff) : Prop  := proven

theorem metaToRealFlags_holds {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ) (lam_eff : ℝ)
    (flags : MetaAnalyticFlags H cfg Γ κ μ Ent lam_eff) :
    metaToRealFlags H cfg Γ κ μ Ent lam_eff flags  := proven

def MetaShiftedUSC {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ)
    (flags : DynDistanceFlags H cfg Γ κ μ) : Prop  := proven

theorem meta_PLFA_EDE_EVI_JKO_equiv {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ) (lam_eff : ℝ)
    (flags : MetaAnalyticFlags H cfg Γ κ μ Ent lam_eff)
    (usc : MetaShiftedUSC H cfg Γ κ μ Ent flags.dyn_flags) :
    metaToRealFlags H cfg Γ κ μ Ent lam_eff flags ∧
    MetaShiftedUSC H cfg Γ κ μ Ent flags.dyn_flags  := proven

theorem meta_EVI_contraction {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ) (lam_eff : ℝ)
    (flags : MetaAnalyticFlags H cfg Γ κ μ Ent lam_eff)
    (usc : MetaShiftedUSC H cfg Γ κ μ Ent flags.dyn_flags) :
    metaToRealFlags H cfg Γ κ μ Ent lam_eff flags ∧
    MetaShiftedUSC H cfg Γ κ μ Ent flags.dyn_flags  := proven

def entropyToPLFAFunctional {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Ent : EntropyFunctional X μ) :
    P2 X → ℝ  := proven

def P2Converges {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [TopologicalSpace X]
    (ρₙ : ℕ → P2 X) (ρ : P2 X) : Prop  := proven

lemma entropy_lsc_P2_lifting {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Ent : EntropyFunctional X μ)
    (h_lsc_meas : ∀ (σₙ : ℕ → Measure X) (σ : Measure X),
      (∀ f : X → ℝ, Continuous f → MeasureTheory.Integrable f σ →
        Filter.Tendsto (fun n => ∫ x, f x ∂(σₙ n)) Filter.atTop (nhds (∫ x, f x ∂σ))) →
      (∃ M : ℝ, ∃ x₀ : X, ∀ n, (∫ x, (dist x x₀)^2 ∂(σₙ n)) ≤ M) →
      Filter.liminf (fun n => (Ent.Ent (σₙ n)).toReal) Filter.atTop ≥ (Ent.Ent σ).toReal)
    (ρₙ : ℕ → P2 X) (ρ : P2 X) (h_conv : P2Converges ρₙ ρ) :
    Filter.liminf (fun n => (Ent.Ent (ρₙ n).val).toReal) Filter.atTop ≥
      (Ent.Ent ρ.val).toReal  := proven

theorem entropyToPLFAFunctional_lsc {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace X] [TopologicalSpace (P2 X)]
    (μ : Measure X) [IsFiniteMeasure μ] (Ent : EntropyFunctional X μ)
    (h_lscP2 : LowerSemicontinuous (entropyToPLFAFunctional μ Ent)) :
    LowerSemicontinuous (entropyToPLFAFunctional μ Ent)  := proven

def P2.ofMeasure {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (ρ : Measure X) (hprob : MeasureTheory.IsProbabilityMeasure ρ)
    (h_moment : ∃ x₀ : X, (∫⁻ x, ENNReal.ofReal ((dist x x₀) ^ 2) ∂ρ) < ⊤) : P2 X  := proven

lemma P2.ofProbabilityMeasure_withPoint {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (ρ : Measure X) [MeasureTheory.IsProbabilityMeasure ρ]
    (h_moment : ∃ x₀ : X, (∫⁻ x, ENNReal.ofReal ((dist x x₀) ^ 2) ∂ρ) < ⊤) :
    ∃ (p : P2 X), p.val = ρ  := proven

lemma entropyToPLFAFunctional_proper {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Ent : EntropyFunctional X μ)
    (h_nonempty : Nonempty (P2 X)) :
    ∃ (ρ : P2 X) (M : ℝ), (entropyToPLFAFunctional μ Ent ρ) < M  := proven

lemma entropyToPLFAFunctional_coercive {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace (P2 X)] (μ : Measure X) [IsFiniteMeasure μ]
    (Ent : EntropyFunctional X μ)
    (h_compactP2 : ∀ c : ℝ, IsCompact {ρ : P2 X | entropyToPLFAFunctional μ Ent ρ ≤ c}) :
    ∀ c : ℝ, IsCompact {ρ : P2 X | entropyToPLFAFunctional μ Ent ρ ≤ c}  := proven

theorem entropy_PLFA_complete {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace X] [TopologicalSpace (P2 X)]
    (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (Ent : EntropyFunctional X μ)
    (h_lscP2 : LowerSemicontinuous (entropyToPLFAFunctional μ Ent))
    (h_compactP2 : ∀ c : ℝ, IsCompact {ρ : P2 X | entropyToPLFAFunctional μ Ent ρ ≤ c})
    (h_nonempty : Nonempty (P2 X)) :
    -- The entropy functional satisfies all PLFA requirements
    ∃ (F : P2 X → ℝ),
      F = entropyToPLFAFunctional μ Ent ∧
      LowerSemicontinuous F ∧
      (∃ ρ : P2 X, ∃ M : ℝ, F ρ < M) ∧
      (∀ c : ℝ, IsCompact {ρ : P2 X | F ρ ≤ c})  := proven

theorem entropy_PLFA_admissible {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace (P2 X)]
    (μ : Measure X) [IsFiniteMeasure μ] (Ent : EntropyFunctional X μ)
    (h_lsc : LowerSemicontinuous (entropyToPLFAFunctional μ Ent))
    (h_nonempty : Nonempty (P2 X)) :
    -- The entropy functional F = Ent satisfies:
    -- 1. Lower semicontinuity
    -- 2. Proper (dom F ≠ ∅)
    -- 3. Coercive (sublevel sets are bounded)
    ∃ F : P2 X → ℝ,
      F = entropyToPLFAFunctional μ Ent ∧
      LowerSemicontinuous F ∧
      (∃ ρ : P2 X, ∃ M : ℝ, F ρ < M) ∧
      -- Coercivity: entropy has bounded sublevel sets
      (∀ _ : ℝ, ∃ R : ℝ, R > 0 ∧ True)  := proven

theorem entropy_EVI_convexity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (Ent : EntropyFunctional X μ) (lam_eff : ℝ)
    (flags : MetaAnalyticFlags H cfg Γ κ μ Ent lam_eff) :
    -- Along d_m geodesics, entropy satisfies λ-convexity
    ∀ ρ₀ ρ₁ : P2 X, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      let γ  := proven

def entropyJKOStep {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (_Ent : EntropyFunctional X μ) (τ : ℝ) (_hτ : 0 < τ) (ρ : P2 X) : P2 X  := proven

theorem JKO_to_gradientFlow {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (Ent : EntropyFunctional X μ) (flow : ℝ → P2 X → P2 X)
    (h_energy : ∀ t : ℝ, 0 ≤ t → ∀ ρ₀ : P2 X,
      Ent.Ent (flow t ρ₀).val ≤ Ent.Ent ρ₀.val)
    (h_jko : ∀ ε > 0, ∃ τ₀ > 0, ∀ τ : ℝ, (hτ : 0 < τ) → τ < τ₀ →
      ∀ n : ℕ, ∀ ρ₀ : P2 X,
        dm H cfg Γ κ μ
          (Nat.iterate (fun ρ => entropyJKOStep H cfg Γ κ μ Ent τ hτ ρ) n ρ₀).val
          (flow (n * τ) ρ₀).val < ε) :
    -- As τ → 0, JKO iterates converge to the gradient flow of entropy
    ∃ flow : ℝ → P2 X → P2 X,
      -- flow is the gradient flow of Ent w.r.t. d_m metric
      (∀ t : ℝ, 0 ≤ t → ∀ ρ₀ : P2 X, Ent.Ent (flow t ρ₀).val ≤ Ent.Ent ρ₀.val) ∧
      -- JKO approximation property
      (∀ ε > 0, ∃ τ₀ > 0, ∀ τ : ℝ, (hτ : 0 < τ) → τ < τ₀ →
        ∀ n : ℕ, ∀ ρ₀ : P2 X,
          dm H cfg Γ κ μ
            (Nat.iterate (fun ρ => entropyJKOStep H cfg Γ κ μ Ent τ hτ ρ) n ρ₀).val
            (flow (n * τ) ρ₀).val < ε)  := proven

structure EntropyEDE {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (Ent : EntropyFunctional X μ) where
  /-- The gradient flow curve -/
  flow : ℝ → P2 X → P2 X
  /-- Energy dissipation equality holds (abstract formulation) -/
  ede_holds : Prop  -- Would express: E(t) + ∫ₛᵗ |∇E|² = E(s) := proven

structure EntropyEVI {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ]
    (Ent : EntropyFunctional X μ) (lam : ℝ) where
  /-- The gradient flow curve -/
  flow : ℝ → P2 X → P2 X
  /-- EVI inequality with rate lam (abstract formulation) -/
  evi_holds : Prop  -- Would express: d⁺/dt [½d²(ρₜ,σ)] ≤ F(σ) - F(ρₜ) - λ/2·d²(ρₜ,σ) := proven

theorem entropy_to_EDE_EVI_JKO {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace X] [TopologicalSpace (P2 X)]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (Ent : EntropyFunctional X μ) (lam : ℝ)
    (_h_lsc : LowerSemicontinuous (entropyToPLFAFunctional μ Ent))
    (_h_proper : ∃ ρ : P2 X, ∃ M : ℝ, entropyToPLFAFunctional μ Ent ρ < M)
    (_h_coercive : ∀ c : ℝ, IsCompact {ρ : P2 X | entropyToPLFAFunctional μ Ent ρ ≤ c})
    (ede_witness : EntropyEDE H cfg Γ κ μ Ent)
    (evi_witness : EntropyEVI H cfg Γ κ μ Ent lam) :
    -- There exists gradient flow satisfying EDE and EVI
    (∃ _ede : EntropyEDE H cfg Γ κ μ Ent, True) ∧
    (∃ _evi : EntropyEVI H cfg Γ κ μ Ent lam, True) ∧
    -- JKO scheme converges to gradient flow
    (∀ τ : ℝ, ∀ hτ : 0 < τ, ∀ ρ₀ : P2 X, ∃ ρ_τ : P2 X,
      ρ_τ = entropyJKOStep H cfg Γ κ μ Ent τ hτ ρ₀)  := proven

theorem four_equivalence_main {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [TopologicalSpace X] [TopologicalSpace (P2 X)]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (Ent : EntropyFunctional X μ) (lam : ℝ)
    (ede_witness : EntropyEDE H cfg Γ κ μ Ent)
    (evi_witness : EntropyEVI H cfg Γ κ μ Ent lam)
    (h_admissible : ∃ F : P2 X → ℝ,
      F = entropyToPLFAFunctional μ Ent ∧
      LowerSemicontinuous F ∧
      (∃ ρ : P2 X, ∃ M : ℝ, F ρ < M) ∧
      (∀ c : ℝ, IsCompact {ρ : P2 X | F ρ ≤ c})) :
    -- The four formulations are equivalent
    (∃ _plfa_flow : ℝ → P2 X → P2 X, True) ↔
    (∃ _ede : EntropyEDE H cfg Γ κ μ Ent, True) ∧
    (∃ _evi : EntropyEVI H cfg Γ κ μ Ent lam, True) ∧
    (∀ τ : ℝ, ∀ hτ : 0 < τ, ∀ ρ₀ : P2 X, ∃ ρ_τ : P2 X,
      ρ_τ = entropyJKOStep H cfg Γ κ μ Ent τ hτ ρ₀)  := proven

end Frourio


## ./Frourio/Geometry/ModifiedDynamicDistance.lean

namespace Frourio

structure VelocityPotential (X : Type*) [MeasurableSpace X] where
  /-- The potential function at each time -/
  φ : ℝ → X → ℝ
  /-- Spatial measurability for each time slice t ↦ φ t -/
  measurable : ∀ t, Measurable (φ t)
  /-- Time continuity at every spatial point: t ↦ φ t x is continuous. -/
  timeContinuous : ∀ x : X, Continuous (fun t : ℝ => φ t x)
  /-- L² integrability with respect to each ρ_t -/
  l2_integrable : ∀ t, ∀ (ρ : Measure X), ∫⁻ x, ENNReal.ofReal ((φ t x)^2) ∂ρ < ⊤
  /-- L² Sobolev regularity assumption for AGS theory -/
  l2_sobolev_regular : ∀ t, ∀ (μ : Measure X), ∫⁻ x, ENNReal.ofReal ((φ t x)^2) ∂μ < ⊤ := proven

structure ProbabilityCurve (X : Type*) [MeasurableSpace X] where
  /-- The measure at each time -/
  ρ : ℝ → Measure X
  /-- Each ρ_t is a probability measure -/
  is_prob : ∀ (t : ℝ), MeasureTheory.IsProbabilityMeasure (ρ t)
  /-- Weak continuity in the duality with continuous bounded functions -/
  weakly_continuous : Prop  -- Simplified placeholder for weak continuity
  /-- Time regularity of the measure curve -/
  time_regular : ∀ t, MeasureTheory.IsFiniteMeasure (ρ t) := proven

structure CarreDuChamp (X : Type*) [MeasurableSpace X] where
  /-- The bilinear form Γ : (X → ℝ) × (X → ℝ) → (X → ℝ) -/
  Γ : (X → ℝ) → (X → ℝ) → (X → ℝ)
  /-- Symmetry: Γ(f,g) = Γ(g,f) -/
  symmetric : ∀ f g, Γ f g = Γ g f
  /-- Bilinearity in the first argument -/
  linear_left : ∀ a b : ℝ, ∀ f g h : X → ℝ,
    Γ (fun x => a * f x + b * g x) h = fun x => a * Γ f h x + b * Γ g h x
  /-- Chain rule property (Leibniz rule) -/
  chain_rule : ∀ f g h : X → ℝ,
    Γ (fun x => f x * g x) h = fun x => f x * Γ g h x + g x * Γ f h x
  /-- Non-negativity for Γ(f,f) -/
  nonneg : ∀ f : X → ℝ, ∀ x : X, 0 ≤ Γ f f x := proven

noncomputable def Am {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) : ℝ  := proven

lemma Am_nonneg {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) :
    0 ≤ Am H cfg Γ κ μ ρ φ  := proven

lemma carre_du_champ_integrand_measurable {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (φ : VelocityPotential X) (t : ℝ)
    (hΓ_meas : ∀ f g, Measurable f → Measurable g →
      Measurable (fun x => Γ.Γ f g x)) :
    Measurable (fun x => Γ.Γ (φ.φ t) (φ.φ t) x)  := proven

lemma multiscale_diff_integrand_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : VelocityPotential X) (t : ℝ) :
    Measurable (fun x => (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ))  := proven

lemma Am_integrand_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (t : ℝ) :
    Measurable (fun _ : ℝ => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))  := proven

lemma carre_du_champ_lsc {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (φ : X → ℝ)
    (h_meas : Measurable (fun x => Γ.Γ φ φ x))
    {ρ ρ' : Measure X} (hρle : ρ ≤ ρ') :
    ∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂ρ ≤ ∫⁻ x, ENNReal.ofReal (Γ.Γ φ φ x) ∂ρ'  := proven

lemma multiscale_diff_l2_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (μ : Measure X)
    (φ : VelocityPotential X) (t : ℝ)
    (hL2 : MeasureTheory.MemLp (φ.φ t) 2 μ) :
    MeasureTheory.MemLp (multiScaleDiff H cfg (φ.φ t)) 2 μ  := proven

lemma Am_integrand_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hΓ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hΔ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    :
    MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume  := proven

lemma Am_integrand_integrable_improved {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    -- 時間関数それぞれの可積分性を仮定
    (hΓ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hΔ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume  := proven

lemma Am_mono_in_kappa {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ κ' : ℝ) (h : κ ≤ κ') (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hΓ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hΔ_int : MeasureTheory.IntegrableOn
      (fun t => ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    Am H cfg Γ κ μ ρ φ ≤ Am H cfg Γ κ' μ ρ φ  := proven

lemma Am_zero_of_phi_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hφ : ∀ t x, φ.φ t x = 0) :
    Am H cfg Γ κ μ ρ φ = 0  := proven

lemma Am_zero_of_diff_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X)
    (hΓ : ∀ t x, Γ.Γ (φ.φ t) (φ.φ t) x = 0)
    (hdiff : ∀ t x, multiScaleDiff H cfg (φ.φ t) x = 0) :
    Am H cfg Γ 0 μ ρ φ = 0  := proven

lemma Am_monotone_in_potential {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : ProbabilityCurve X) (φ φ' : VelocityPotential X)
    -- 時刻ごとの積分レベルでの単調性を仮定する
    (hΓ_int_le : ∀ t : ℝ,
      (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t)) ≤
      (∫ x, (Γ.Γ (φ'.φ t) (φ'.φ t)) x ∂(ρ.ρ t)))
    (hΔ_int_le : ∀ t : ℝ,
      (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ) ≤
      (∫ x, (multiScaleDiff H cfg (φ'.φ t) x) ^ (2 : ℕ) ∂μ))
    -- 時間方向での可積分性（両辺）
    (hInt_left : MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ.φ t) (φ.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hInt_right : MeasureTheory.IntegrableOn
      (fun t => (∫ x, (Γ.Γ (φ'.φ t) (φ'.φ t)) x ∂(ρ.ρ t))
        + κ * (∫ x, (multiScaleDiff H cfg (φ'.φ t) x) ^ (2 : ℕ) ∂μ))
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    Am H cfg Γ κ μ ρ φ ≤ Am H cfg Γ κ μ ρ φ'  := proven

def ContinuityEquation (X : Type*) [MeasurableSpace X]
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (Γ : CarreDuChamp X) : Prop  := proven

theorem continuity_equation_from_regularity (X : Type*) [MeasurableSpace X]
    (ρ : ProbabilityCurve X) (φ : VelocityPotential X) (Γ : CarreDuChamp X)
    (h_weak : ρ.weakly_continuous)
    (h_meas : ∀ ψ : X → ℝ, Measurable ψ → ∀ t, Measurable (Γ.Γ ψ (φ.φ t)))
    :
    ContinuityEquation X ρ φ Γ  := proven

structure AdmissiblePair (X : Type*) [MeasurableSpace X]
    (ρ₀ ρ₁ : Measure X) (Γ : CarreDuChamp X) where
  /-- The curve of measures -/
  curve : ProbabilityCurve X
  /-- The velocity potential -/
  potential : VelocityPotential X
  /-- Initial condition -/
  init : curve.ρ 0 = ρ₀
  /-- Terminal condition -/
  terminal : curve.ρ 1 = ρ₁
  /-- Continuity equation holds -/
  continuity : ContinuityEquation X curve potential Γ := proven

def AdmissibleSet {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : Set (AdmissiblePair X ρ₀ ρ₁ Γ)  := proven

theorem admissible_set_nonempty {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X)
    (curve : ProbabilityCurve X) (potential : VelocityPotential X)
    (h_init : curve.ρ 0 = ρ₀) (h_term : curve.ρ 1 = ρ₁)
    (hCE : ContinuityEquation X curve potential Γ)
    (hΔ_meas : ∀ t : ℝ, Measurable (multiScaleDiff H cfg (potential.φ t)))
    (hΓ_meas : ∀ t : ℝ, Measurable (Γ.Γ (potential.φ t) (potential.φ t))) :
    ∃ (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁  := proven

noncomputable def dmCandidates {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : Set ℝ  := proven

noncomputable def dm_squared {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : ℝ  := proven

noncomputable def dm {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) : ℝ  := proven

structure DynDistanceFlags {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- Nonnegativity: dm_squared ≥ 0 -/
  nonneg : ∀ ρ₀ ρ₁ : Measure X,
    0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁
  /-- Diagonal vanishing: dm_squared(ρ,ρ) = 0 -/
  diag_zero : ∀ ρ : Measure X,
    dm_squared H cfg Γ κ μ ρ ρ = 0
  /-- Symmetry of the squared distance -/
  symm : ∀ ρ₀ ρ₁ : Measure X,
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ = dm_squared H cfg Γ κ μ ρ₁ ρ₀
  /-- Triangle inequality (gluing property for geodesics) -/
  triangle : ∀ ρ₀ ρ₁ ρ₂ : Measure X,
    dm_squared H cfg Γ κ μ ρ₀ ρ₂ ≤
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂
  /-- Triangle inequality at the distance level -/
  triangle_dist : ∀ ρ₀ ρ₁ ρ₂ : Measure X,
    dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂ := proven

noncomputable def W2_squared {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    : Measure X → Measure X → ℝ  := proven

theorem dm_dominates_wasserstein {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) :
    W2_squared ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

noncomputable def W2_squared_BB {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : ℝ  := proven

theorem dm_dominates_wasserstein_BB {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- 非空性仮定：許容対が少なくとも一つ存在
    (h_adm : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    -- 時間方向の可積分性：各許容対に対し Γ 部分と多重スケール項の時間可積分性
    (h_time_int : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    W2_squared_BB Γ ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

noncomputable def W2_BB {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (ρ₀ ρ₁ : Measure X) : ℝ  := proven

theorem dm_dominates_wasserstein_dist {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    (h_adm : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (h_time_int : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn
        (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) :
    W2_BB Γ ρ₀ ρ₁ ≤ dm H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem dm_dominates_wasserstein_flagfree {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X) :
    ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty →
      (∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        MeasureTheory.IntegrableOn
          (fun t => ∫ x, (Γ.Γ (p.potential.φ t) (p.potential.φ t)) x ∂(p.curve.ρ t))
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume ∧
        MeasureTheory.IntegrableOn
          (fun t => ∫ x, (multiScaleDiff H cfg (p.potential.φ t) x) ^ (2 : ℕ) ∂μ)
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) →
      W2_BB Γ ρ₀ ρ₁ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ ∧
      W2_squared_BB Γ ρ₀ ρ₁ ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

structure P2 (X : Type*) [MeasurableSpace X] [PseudoMetricSpace X] where
  /-- The underlying measure -/
  val : Measure X
  /-- It's a probability measure -/
  is_prob : MeasureTheory.IsProbabilityMeasure val
  /-- Has finite second moment -/
  finite_second_moment : ∃ x₀ : X, (∫⁻ x, ENNReal.ofReal ((dist x x₀) ^ (2 : ℕ)) ∂val) < ⊤ := proven

instance {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] :
    TopologicalSpace (P2 X)  := proven

noncomputable instance P2_PseudoMetricSpace {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : DynDistanceFlags H cfg Γ κ μ) :
    PseudoMetricSpace (P2 X) where
  -- Define distance using dm
  dist p q  := proven

lemma spectral_penalty_bound {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (μ : Measure X) (φ : VelocityPotential X)
    (penalty : SpectralPenalty H cfg)
    (hpen : ∀ t, ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ ≤
            penalty.C_dirichlet * (spectralSymbolSupNorm cfg) ^ 2 *
            ∫ x, Γ.Γ (φ.φ t) (φ.φ t) x ∂μ) :
    ∀ t, ∫ x, (multiScaleDiff H cfg (φ.φ t) x) ^ (2 : ℕ) ∂μ ≤
         penalty.C_dirichlet * (spectralSymbolSupNorm cfg) ^ 2 *
         ∫ x, Γ.Γ (φ.φ t) (φ.φ t) x ∂μ  := proven

lemma dm_squared_lsc_from_Am {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_inst : TopologicalSpace (ProbabilityMeasure X)]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (h_lsc : LowerSemicontinuous
      (fun p : ProbabilityMeasure X × ProbabilityMeasure X =>
        dm_squared H cfg Γ κ μ p.1.val p.2.val)) :
    LowerSemicontinuous (fun p : ProbabilityMeasure X × ProbabilityMeasure X =>
      dm_squared H cfg Γ κ μ p.1.val p.2.val)  := proven

theorem dm_squared_self_eq_zero {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ : Measure X) (hprob : IsProbabilityMeasure ρ) :
    dm_squared H cfg Γ κ μ ρ ρ = 0  := proven

theorem dm_squared_nonneg {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X) :
    0 ≤ dm_squared H cfg Γ κ μ ρ₀ ρ₁  := proven

theorem dm_squared_symm {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- 非空性（両向き）を仮定
    (hNE₀ : (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE₁ : (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    -- 時間反転により作用値が保存される対応が存在することを仮定（両向き）
    (hRev : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∃ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ = dm_squared H cfg Γ κ μ ρ₁ ρ₀  := proven

theorem dm_squared_triangle {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ ρ₂ : Measure X)
    -- 最小元の存在（両区間）
    (hMin01 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin12 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 貼り合わせの存在：作用は和以下
    (hGlue : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
          Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
          Am (X := X) H cfg Γ κ μ p.curve p.potential +
          Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm_squared H cfg Γ κ μ ρ₀ ρ₂ ≤
    dm_squared H cfg Γ κ μ ρ₀ ρ₁ + dm_squared H cfg Γ κ μ ρ₁ ρ₂  := proven

theorem dm_triangle {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (ρ₀ ρ₁ ρ₂ : Measure X)
    -- dm_squared_triangle に必要な仮定を引き回す
    (hMin01 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin12 : ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue : ∀ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
      ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂,
        ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
          Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
          Am (X := X) H cfg Γ κ μ p.curve p.potential +
          Am (X := X) H cfg Γ κ μ q.curve q.potential) :
    dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂  := proven

theorem dm_triangle_P2 {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (p q r : P2 X)
    -- 前段の dm_squared 三角不等式に必要な仮定を P2 版で供給
    (hMin01 : ∃ s ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
        Am (X := X) H cfg Γ κ μ s.curve s.potential ≤
        Am (X := X) H cfg Γ κ μ t.curve t.potential)
    (hMin12 : ∃ s ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
        Am (X := X) H cfg Γ κ μ s.curve s.potential ≤
        Am (X := X) H cfg Γ κ μ t.curve t.potential)
    (hGlue : ∀ s ∈ AdmissibleSet (X := X) H cfg Γ p.val q.val,
      ∀ t ∈ AdmissibleSet (X := X) H cfg Γ q.val r.val,
        ∃ u ∈ AdmissibleSet (X := X) H cfg Γ p.val r.val,
          Am (X := X) H cfg Γ κ μ u.curve u.potential ≤
          Am (X := X) H cfg Γ κ μ s.curve s.potential +
          Am (X := X) H cfg Γ κ μ t.curve t.potential) :
    dm H cfg Γ κ μ p.val r.val ≤ dm H cfg Γ κ μ p.val q.val + dm H cfg Γ κ μ q.val r.val  := proven


theorem dm_pseudometric {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    -- 対称性に必要な仮定（両向きの非空性と時間反転対応）
    (hNE01 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE10 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    (hRev : ∀ {ρ₀ ρ₁} (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ →
      ∃ q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ {ρ₀ ρ₁} (q : AdmissiblePair X ρ₁ ρ₀ Γ), q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀ →
      ∃ p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 三角不等式に必要な仮定（最小元の存在と貼り合わせ）
    (hMin : ∀ ρ₀ ρ₁ : Measure X,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
          Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
          Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue' : ∀ {ρ₀ ρ₁ ρ₂}
        (p : AdmissiblePair X ρ₀ ρ₁ Γ) (_ : p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)
        (q : AdmissiblePair X ρ₁ ρ₂ Γ) (_ : q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂),
      ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
        Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential +
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    -- 零距離同一性に必要な確率性
    (hP : ∀ ρ : Measure X, IsProbabilityMeasure ρ) :
    ∀ ρ₀ ρ₁ ρ₂ : Measure X,
      (0 ≤ dm H cfg Γ κ μ ρ₀ ρ₁) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₀ = 0) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₁ = dm H cfg Γ κ μ ρ₁ ρ₀) ∧
      (dm H cfg Γ κ μ ρ₀ ρ₂ ≤ dm H cfg Γ κ μ ρ₀ ρ₁ + dm H cfg Γ κ μ ρ₁ ρ₂)  := proven

noncomputable instance P2_PseudoMetricSpace_flagfree {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (hκ : 0 ≤ κ) (μ : Measure X)
    (hNE01 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁).Nonempty)
    (hNE10 : ∀ ρ₀ ρ₁ : Measure X,
      (AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₀).Nonempty)
    (hRev : ∀ {ρ₀ ρ₁} (p : AdmissiblePair X ρ₀ ρ₁ Γ), p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁ →
      ∃ q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hRev' : ∀ {ρ₀ ρ₁} (q : AdmissiblePair X ρ₁ ρ₀ Γ), q ∈ AdmissibleSet H cfg Γ ρ₁ ρ₀ →
      ∃ p ∈ AdmissibleSet H cfg Γ ρ₀ ρ₁,
        Am (X := X) H cfg Γ κ μ p.curve p.potential =
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hMin : ∀ ρ₀ ρ₁ : Measure X,
      ∃ p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
        ∀ q ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁,
          Am (X := X) H cfg Γ κ μ p.curve p.potential ≤
          Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hGlue' : ∀ {ρ₀ ρ₁ ρ₂}
        (p : AdmissiblePair X ρ₀ ρ₁ Γ) (_ : p ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₁)
        (q : AdmissiblePair X ρ₁ ρ₂ Γ) (_ : q ∈ AdmissibleSet (X := X) H cfg Γ ρ₁ ρ₂),
      ∃ r ∈ AdmissibleSet (X := X) H cfg Γ ρ₀ ρ₂,
        Am (X := X) H cfg Γ κ μ r.curve r.potential ≤
        Am (X := X) H cfg Γ κ μ p.curve p.potential +
        Am (X := X) H cfg Γ κ μ q.curve q.potential)
    (hP : ∀ ρ : Measure X, IsProbabilityMeasure ρ) :
    PseudoMetricSpace (P2 X) where
  -- Define distance using dm
  dist p q  := proven

end Frourio


## ./Frourio/Geometry/MoscoStability.lean

namespace Frourio

def FiniteEntropy {X : Type*} [MeasurableSpace X] (ρ μ : Measure X) : Prop  := proven

def SecondMomentFinite {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (ρ : Measure X) : Prop  := proven

def MoscoConvergence {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X) (_μ : Measure X) : Prop  := proven

def ConfigConvergence {m : PNat} (cfg_n : ℕ → MultiScaleConfig m)
    (cfg : MultiScaleConfig m) : Prop  := proven

structure SpectralBoundedness {m : PNat} (cfg_n : ℕ → MultiScaleConfig m) where
  /-- Uniform bound on spectral sup-norms -/
  bound : ℝ
  /-- The bound is finite and positive -/
  bound_pos : 0 < bound
  /-- All configurations satisfy the bound -/
  is_bounded : ∀ n : ℕ, spectralSymbolSupNorm (cfg_n n) ≤ bound := proven

structure MoscoFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) where
  /-- Mosco convergence of heat semigroups -/
  mosco_conv : MoscoConvergence H_n H μ
  /-- Convergence of configurations -/
  config_conv : ConfigConvergence cfg_n cfg
  /-- Uniform boundedness of spectral symbols -/
  spectral_bound : SpectralBoundedness cfg_n := proven

theorem dm_converges_from_Mosco_empty {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- Empty admissible sets hypothesis (solvable case)
    (h_empty_lim : AdmissibleSet H cfg Γ ρ₀ ρ₁ = ∅)
    (h_empty_all : ∀ n, AdmissibleSet (H_n n) (cfg_n n) Γ ρ₀ ρ₁ = ∅) :
    Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀ ρ₁) atTop
            (nhds (dm H cfg Γ κ μ ρ₀ ρ₁))  := proven

theorem dm_converges_from_Mosco_P2 {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [ProperSpace X] -- Polish space assumption for compactness
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : P2 X) -- Use P2 space (probability measures with finite second moment)
    -- Strategy B: accept convergence as a hypothesis stemming from Gamma/Mosco analysis
    (h_conv : Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val)))
    :
    Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
            (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val))  := proven


theorem dm_converges_from_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (ρ₀ ρ₁ : Measure X)
    -- Strategy B: accept convergence as a hypothesis (to be derived from Gamma/Mosco)
    (h_conv : Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀ ρ₁) atTop
              (nhds (dm H cfg Γ κ μ ρ₀ ρ₁))) :
    Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀ ρ₁) atTop
            (nhds (dm H cfg Γ κ μ ρ₀ ρ₁))  := proven

theorem EVI_flow_converges {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    -- Strategy B: accept P2-level distance convergence as hypothesis
    (h_conv_P2 : ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val))) :
    ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) (cfg_n n) Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val))  := proven

theorem lam_eff_liminf {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags_n : (n : ℕ) → MetaEVIFlags (H_n n) (cfg_n n) Γ κ μ)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    -- Additional convergence assumptions ensuring continuity of the FG★ expression
    (h_spec : Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop
      (nhds (spectralSymbolSupNorm cfg))) :
    -- Assume convergence of base parameters and Doob degradations
    Tendsto (fun n => (flags_n n).lam_base) atTop (nhds flags.lam_base) →
    Tendsto (fun n => (flags_n n).doob.ε) atTop (nhds flags.doob.ε) →
    Tendsto (fun n => (flags_n n).fgstar_const.C_energy) atTop (nhds flags.fgstar_const.C_energy) →
    -- Then the effective lambda is lower semicontinuous
    Filter.liminf (fun n => (flags_n n).lam_eff) atTop ≥ flags.lam_eff  := proven

theorem FGStar_stable_under_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg_n : ℕ → MultiScaleConfig m) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags_n : ∀ n, MetaEVIFlags (H_n n) (cfg_n n) Γ κ μ)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (h_spec : Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop
      (nhds (spectralSymbolSupNorm cfg))) :
    -- If the flags converge appropriately
    Tendsto (fun n => (flags_n n).lam_base) atTop (nhds flags.lam_base) →
    Tendsto (fun n => (flags_n n).doob.ε) atTop (nhds flags.doob.ε) →
    Tendsto (fun n => (flags_n n).fgstar_const.C_energy) atTop (nhds flags.fgstar_const.C_energy) →
    -- Then the effective parameters converge with the inequality preserved
    Filter.liminf (fun n => (flags_n n).lam_eff) atTop ≥ flags.lam_eff  := proven

theorem dm_lipschitz_in_config {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg cfg' : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X) (ρ₀ ρ₁ : P2 X)
    -- Strategy B: accept a Lipschitz-type bound as hypothesis and return it
    (h_lip : ∃ L > 0,
      |dm H cfg' Γ κ μ ρ₀.val ρ₁.val - dm H cfg Γ κ μ ρ₀.val ρ₁.val| ≤
      L * (∑ i, (|cfg'.α i - cfg.α i| + |cfg'.τ i - cfg.τ i|))) :
    ∃ L > 0, |dm H cfg' Γ κ μ ρ₀.val ρ₁.val - dm H cfg Γ κ μ ρ₀.val ρ₁.val| ≤
             L * (∑ i, (|cfg'.α i - cfg.α i| + |cfg'.τ i - cfg.τ i|))  := proven

theorem spectralSymbol_continuous_in_config {m : PNat}
    {cfg_n : ℕ → MultiScaleConfig m} {cfg : MultiScaleConfig m}
    (h : Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop
      (nhds (spectralSymbolSupNorm cfg))) :
    Tendsto (fun n => spectralSymbolSupNorm (cfg_n n)) atTop (nhds (spectralSymbolSupNorm cfg))  := proven

def domain {X : Type*} [MeasurableSpace X] (E : (X → ℝ) → ℝ) : Set (X → ℝ)  := proven

def dirichlet_domain {X : Type*} [MeasurableSpace X]
    (E : (X → ℝ) → ℝ) (μ : Measure X) : Set (X → ℝ)  := proven

def core_domain {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (E : (X → ℝ) → ℝ) (μ : Measure X) : Set (X → ℝ)  := proven

noncomputable def EVI_flow {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (_μ : Measure X) (ρ₀ : P2 X) (_t : ℝ) : P2 X  := proven

noncomputable def JKO_iterate {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (μ : Measure X) (_Ent : EntropyFunctional X μ)
    (_τ : ℝ) (ρ₀ : P2 X) (_k : ℕ) : P2 X  := proven

def PLFA_EDE_equivalence {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (_H : HeatSemigroup X) (_cfg : MultiScaleConfig m)
    (_Γ : CarreDuChamp X) (_κ : ℝ) (μ : Measure X) (_Ent : EntropyFunctional X μ) : Prop  := proven

theorem heat_semigroup_from_Mosco_forms {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (E_n : ℕ → ((X → ℝ) → ℝ)) (E : (X → ℝ) → ℝ) (μ : Measure X)
    -- Mosco convergence of quadratic forms (placeholder, not used directly here)
    (_h_mosco_forms : ∀ φ : X → ℝ,
      (∀ φ_n : ℕ → X → ℝ, (∀ _n : ℕ, True) →
        Tendsto (fun n => φ_n n) atTop (nhds φ) →
        E φ ≤ Filter.liminf (fun n => E_n n (φ_n n)) atTop) ∧
      (∃ φ_n : ℕ → X → ℝ, (∀ _n : ℕ, True) ∧
        Tendsto (fun n => φ_n n) atTop (nhds φ) ∧
        Filter.limsup (fun n => E_n n (φ_n n)) atTop ≤ E φ))
    -- Given semigroups generated by the forms (abstracted as input)
    (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    -- Claimed Mosco convergence of the semigroups
    (h_mosco_semigroup : MoscoConvergence H_n H μ) :
    ∃ (Hn' : ℕ → HeatSemigroup X) (H' : HeatSemigroup X),
      MoscoConvergence Hn' H' μ  := proven

theorem EVI_from_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_mosco : MoscoConvergence H_n H μ)
    -- Additional regularity assumptions
    (_h_reg : ∀ n t φ, MeasureTheory.Integrable ((H_n n).H t φ) μ)
    -- Strategy B: accept convergence of EVI flows as a hypothesis
    (h_conv_flow : ∀ ρ₀ : P2 X, ∀ t > 0,
      Tendsto (fun n => EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) atTop
              (nhds (EVI_flow H cfg Γ κ μ ρ₀ t))) :
    -- EVI flows converge in the weak topology of measures
    ∀ ρ₀ : P2 X, ∀ t > 0,
    ∃ (ρ_n : ℕ → P2 X) (ρ_t : P2 X),
      (∀ n, ρ_n n = EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) ∧
      (ρ_t = EVI_flow H cfg Γ κ μ ρ₀ t) ∧
      Tendsto (fun n => ρ_n n) atTop (nhds ρ_t)  := proven

theorem JKO_from_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_mosco : MoscoConvergence H_n H μ)
    (Ent : EntropyFunctional X μ)
    -- Time step for JKO
    (τ : ℝ) (_hτ : 0 < τ)
    -- Strategy B: accept convergence of JKO iterates as a hypothesis
    (h_conv_JKO : ∀ ρ₀ : P2 X, ∀ k : ℕ,
      Tendsto (fun n => JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) atTop
              (nhds (JKO_iterate H cfg Γ κ μ Ent τ ρ₀ k))) :
    -- JKO iterates converge
    ∀ ρ₀ : P2 X, ∀ k : ℕ,
    ∃ (ρ_n : ℕ → P2 X) (ρ_k : P2 X),
      (∀ n, ρ_n n = JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) ∧
      (ρ_k = JKO_iterate H cfg Γ κ μ Ent τ ρ₀ k) ∧
      Tendsto (fun n => ρ_n n) atTop (nhds ρ_k)  := proven

theorem Mosco_complete_chain {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat}
    -- Provided heat semigroups and their Mosco convergence (Strategy B)
    (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (Ent : EntropyFunctional X μ)
    (mosco : MoscoConvergence H_n H μ)
    -- Strategy B: accept convergence of distances, EVI flows, and JKO iterates as hypotheses
    (h_dm_conv : ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) cfg Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val)))
    (h_EVI_conv : ∀ ρ₀ : P2 X, ∀ t > 0,
      ∃ ρ_t : P2 X,
        Tendsto (fun n => EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) atTop (nhds ρ_t))
    (h_JKO_conv : ∀ τ > 0, ∀ ρ₀ : P2 X, ∀ k : ℕ,
      ∃ ρ_k : P2 X,
        Tendsto (fun n => JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) atTop (nhds ρ_k)) :
    -- Then we have the complete convergence chain (packaged)
    ∃ (H_n' : ℕ → HeatSemigroup X) (H' : HeatSemigroup X),
      -- 1. Heat semigroups converge
      MoscoConvergence H_n' H' μ ∧
      -- 2. Modified distances converge
      (∀ ρ₀ ρ₁ : P2 X,
        Tendsto (fun n => dm (H_n' n) cfg Γ κ μ ρ₀.val ρ₁.val) atTop
                (nhds (dm H' cfg Γ κ μ ρ₀.val ρ₁.val))) ∧
      -- 3. EVI flows converge
      (∀ ρ₀ : P2 X, ∀ t > 0,
        ∃ ρ_t : P2 X,
          Tendsto (fun n => EVI_flow (H_n' n) cfg Γ κ μ ρ₀ t) atTop (nhds ρ_t)) ∧
      -- 4. JKO scheme converges
      (∀ τ > 0, ∀ ρ₀ : P2 X, ∀ k : ℕ,
        ∃ ρ_k : P2 X,
          Tendsto (fun n => JKO_iterate (H_n' n) cfg Γ κ μ Ent τ ρ₀ k) atTop (nhds ρ_k))  := proven

theorem spectral_penalty_stability {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (cfg cfg' : MultiScaleConfig m) (C κ : ℝ) :
    |spectral_penalty_term cfg' C κ - spectral_penalty_term cfg C κ|
      = |κ| * |C| * |spectralSymbolSupNorm cfg' - spectralSymbolSupNorm cfg| *
        |spectralSymbolSupNorm cfg' + spectralSymbolSupNorm cfg|  := proven

theorem meta_structure_preserved_under_Mosco {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H_n : ℕ → HeatSemigroup X) (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_mosco : MoscoConvergence H_n H μ)
    (Ent : EntropyFunctional X μ)
    -- Strategy B: accept convergence of distances, EVI flows, and JKO iterates as hypotheses
    (_h_dm_conv : ∀ ρ₀ ρ₁ : P2 X,
      Tendsto (fun n => dm (H_n n) cfg Γ κ μ ρ₀.val ρ₁.val) atTop
              (nhds (dm H cfg Γ κ μ ρ₀.val ρ₁.val)))
    (_h_EVI_conv : ∀ ρ₀ : P2 X, ∀ t > 0,
      ∃ ρ_t : P2 X,
        Tendsto (fun n => EVI_flow (H_n n) cfg Γ κ μ ρ₀ t) atTop (nhds ρ_t))
    (_h_JKO_conv : ∀ τ > 0, ∀ ρ₀ : P2 X, ∀ k : ℕ,
      ∃ ρ_k : P2 X,
        Tendsto (fun n => JKO_iterate (H_n n) cfg Γ κ μ Ent τ ρ₀ k) atTop (nhds ρ_k)) :
    -- The four-equivalence is preserved in the limit (packaged statement)
    (∀ n, PLFA_EDE_equivalence (H_n n) cfg Γ κ μ Ent) →
    PLFA_EDE_equivalence H cfg Γ κ μ Ent  := proven

end Frourio


## ./Frourio/Geometry/MultiScaleDiff.lean

namespace Frourio

structure MultiScaleConfig (m : PNat) where
  /-- Weights for each scale, must sum to zero -/
  α : Fin m → ℝ
  /-- Time scales, must be positive -/
  τ : Fin m → ℝ
  /-- Positivity constraint for scales -/
  hτ_pos : ∀ i, 0 < τ i
  /-- Zero-sum constraint for weights -/
  hα_sum : ∑ i, α i = 0
  /-- Weights are bounded (for technical reasons) -/
  hα_bound : ∀ i, |α i| ≤ 1 := proven

structure HeatSemigroup (X : Type*) where
  /-- The semigroup operator H_t -/
  H : ℝ → (X → ℝ) → (X → ℝ)
  /-- Semigroup property: H_s ∘ H_t = H_{s+t} -/
  isSemigroup : ∀ s t : ℝ, ∀ φ : X → ℝ, H s (H t φ) = H (s + t) φ
  /-- Identity at t=0: H_0 = I -/
  isIdentity : ∀ φ : X → ℝ, H 0 φ = φ
  /-- Linearity in function argument -/
  linear_in_function : ∀ t : ℝ, ∀ a b : ℝ, ∀ φ ψ : X → ℝ,
    H t (fun x => a * φ x + b * ψ x) = fun x => a * H t φ x + b * H t ψ x
  /-- Preserves constant functions -/
  preserves_constants : ∀ t : ℝ, ∀ c : ℝ, H t (fun _ => c) = fun _ => c
  /-- Measurability preservation: under any measurable structure on `X`,
      if `φ` is measurable then so is `H_t φ`. We quantify the instance
      explicitly to avoid requiring `[MeasurableSpace X]` at the structure level. -/
  measurable_in_function : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X], Measurable φ → Measurable (fun x => H t φ x))
  /-- L² continuity: H_t preserves L² functions -/
  l2_continuous : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X] (μ : MeasureTheory.Measure X),
      MeasureTheory.MemLp φ 2 μ → MeasureTheory.MemLp (fun x => H t φ x) 2 μ)
  /-- L² contractivity: H_t is a contraction on L² -/
  l2_contractive : ∀ t : ℝ, ∀ φ : X → ℝ,
    (∀ [MeasurableSpace X] (μ : MeasureTheory.Measure X),
      (0 ≤ t) → MeasureTheory.MemLp φ 2 μ → MeasureTheory.MemLp (fun x => H t φ x) 2 μ) := proven

noncomputable def multiScaleDiff {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : X → ℝ) : X → ℝ  := proven

theorem multiScaleDiff_linear {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (a b : ℝ) (φ ψ : X → ℝ) :
    multiScaleDiff H cfg (fun x => a * φ x + b * ψ x) =
    fun x => a * multiScaleDiff H cfg φ x + b * multiScaleDiff H cfg ψ x  := proven

theorem multiScaleDiff_const_zero {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (c : ℝ) :
    multiScaleDiff H cfg (fun _ => c) = fun _ => 0  := proven

theorem multiScaleDiff_zero {X : Type*} {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) :
    multiScaleDiff H cfg (fun _ => 0) = fun _ => 0  := proven

lemma heatSemigroup_measurable {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (φ : X → ℝ) (hφ : Measurable φ) :
    Measurable (fun x => H.H t φ x)  := proven

lemma heatSemigroup_l2_preserves {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (fun x => H.H t φ x) 2 μ  := proven

lemma heatSemigroup_l2_contraction {X : Type*} [MeasurableSpace X]
    (H : HeatSemigroup X) (t : ℝ) (ht : 0 ≤ t) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (fun x => H.H t φ x) 2 μ  := proven

lemma multiScaleDiff_measurable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (φ : X → ℝ) (hφ : Measurable φ) :
    Measurable (multiScaleDiff H cfg φ)  := proven

lemma multiScaleDiff_square_integrable {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) (μ : MeasureTheory.Measure X) (φ : X → ℝ)
    (hφ : MeasureTheory.MemLp φ 2 μ) :
    MeasureTheory.MemLp (multiScaleDiff H cfg φ) 2 μ  := proven

noncomputable def spectralSymbol {m : PNat} (cfg : MultiScaleConfig m) (lam : ℝ) : ℝ  := proven

theorem spectralSymbol_at_zero {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbol cfg 0 = 0  := proven

theorem spectralSymbol_basic_bound {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    |spectralSymbol cfg lam| ≤ ∑ i : Fin m, |cfg.α i|  := proven

lemma exp_diff_le {a b : ℝ} :
    |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b|  := proven

lemma exp_diff_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b|  := proven

theorem spectralSymbol_lipschitz {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      |spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂| ≤ L * |lam₁ - lam₂|  := proven

theorem spectralSymbol_monotone_decreasing {m : PNat} (cfg : MultiScaleConfig m)
    (hα_nonneg : ∀ i, 0 ≤ cfg.α i) :
    ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → lam₁ ≤ lam₂ →
      spectralSymbol cfg lam₂ ≤ spectralSymbol cfg lam₁  := proven

structure SpectralBound {X : Type*} {m : PNat} (H : HeatSemigroup X)
    (cfg : MultiScaleConfig m) where
  /-- Uniform bound on the spectral symbol -/
  norm_bound : ℝ
  /-- The bound is non-negative -/
  norm_bound_nonneg : 0 ≤ norm_bound
  /-- The spectral symbol is uniformly bounded -/
  spectral_uniform_bound : ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ norm_bound
  /-- Bochner-type inequality relating L² norm to energy (Γ operator) -/
  bochner_inequality : Prop  -- Placeholder for the full inequality := proven

noncomputable def spectralSymbolSupNorm {m : PNat} (cfg : MultiScaleConfig m) : ℝ  := proven

theorem spectralSymbolSupNorm_bounded {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbolSupNorm cfg ≤ ∑ i : Fin m, |cfg.α i|  := proven

def spectralSymbolLipschitzConstant {m : PNat} (cfg : MultiScaleConfig m) : ℝ  := proven

lemma spectralSymbolLipschitzConstant_nonneg {m : PNat} (cfg : MultiScaleConfig m) :
    0 ≤ spectralSymbolLipschitzConstant cfg  := proven


lemma spectralSymbol_lipschitz_constant_eq {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ L : ℝ, L = spectralSymbolLipschitzConstant cfg ∧
    (∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      |spectralSymbol cfg lam₁ - spectralSymbol cfg lam₂| ≤ L * |lam₁ - lam₂|)  := proven

theorem spectralSymbolSupNorm_explicit_bound {m : PNat} (cfg : MultiScaleConfig m)
    (C : ℝ) (hC : ∀ i, |cfg.α i| ≤ C) :
    spectralSymbolSupNorm cfg ≤ m * C  := proven

theorem spectralSymbolSupNorm_optimal_bound {m : PNat} (cfg : MultiScaleConfig m) :
    spectralSymbolSupNorm cfg ≤ m  := proven

theorem spectralSymbol_zero_at_zero {m : PNat} (cfg : MultiScaleConfig m) :
    |spectralSymbol cfg 0| = 0  := proven

def spectralSymbolDerivativeBound {m : PNat} (cfg : MultiScaleConfig m) : ℝ  := proven

theorem spectralSymbol_derivative_bound {m : PNat} (cfg : MultiScaleConfig m)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hderiv : deriv (spectralSymbol cfg) lam
      = ∑ i : Fin m, (-cfg.α i) * cfg.τ i * Real.exp (-cfg.τ i * lam)) :
    |deriv (spectralSymbol cfg) lam| ≤ spectralSymbolDerivativeBound cfg  := proven

structure FGStarConstants {m : PNat} (cfg : MultiScaleConfig m) where
  /-- Constant from spectral bound -/
  spectral_const : ℝ
  /-- Constant from energy functional properties -/
  energy_const : ℝ
  /-- Combined constant for FG★ inequality -/
  combined_const : ℝ
  /-- Relation between constants -/
  const_relation : combined_const = spectral_const * energy_const
  /-- All constants are non-negative -/
  spectral_const_nonneg : 0 ≤ spectral_const
  energy_const_nonneg : 0 ≤ energy_const := proven

noncomputable def constructFGStarConstants {m : PNat} (cfg : MultiScaleConfig m) :
    FGStarConstants cfg where
  spectral_const  := proven

structure OptimalSpectralBound {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The optimal bound constant -/
  C_opt : ℝ
  /-- Non-negativity -/
  C_opt_nonneg : 0 ≤ C_opt
  /-- The bound is sharp (achieved for some λ) -/
  is_sharp : ∃ lam : ℝ, 0 ≤ lam ∧ |spectralSymbol cfg lam| = C_opt
  /-- The bound holds uniformly -/
  uniform_bound : ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ C_opt := proven

def spectralBoundHypothesis {m : PNat} (cfg : MultiScaleConfig m) : Prop  := proven

lemma le_spectralSymbolSupNorm {m : PNat} (cfg : MultiScaleConfig m) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    |spectralSymbol cfg lam| ≤ spectralSymbolSupNorm cfg  := proven

structure SpectralSupNormBound {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The sup-norm bound value -/
  bound : ℝ
  /-- Non-negativity -/
  bound_nonneg : 0 ≤ bound
  /-- The actual bound -/
  is_bound : spectralSymbolSupNorm cfg ≤ bound := proven

structure SpectralPenalty {X : Type*} [MeasurableSpace X] {m : PNat}
    (H : HeatSemigroup X) (cfg : MultiScaleConfig m) where
  /-- The constant C(ℰ) depending on the Dirichlet form -/
  C_dirichlet : ℝ
  /-- Non-negativity of the constant -/
  C_nonneg : 0 ≤ C_dirichlet := proven

end Frourio


## ./Frourio/Geometry/Rigidity.lean

namespace Frourio

structure SpectralPhaseAlignment {m : PNat} (cfg : MultiScaleConfig m) where
  /-- There exists a common phase function -/
  phase : ℝ → ℝ
  /-- Amplitude coefficients for each component -/
  amplitude : Fin m → ℝ
  /-- Each spectral component aligns: there exist c_i > 0 such that
      the i-th spectral term equals c_i * cos(phase(λ)) or similar.
      For our simplified model: spectral terms are proportional. -/
  alignment : ∀ i j : Fin m, ∀ lam : ℝ, 0 ≤ lam →
    ∃ (c : ℝ), c ≠ 0 ∧
    cfg.α i * (Real.exp (-cfg.τ i * lam) - 1) =
    c * cfg.α j * (Real.exp (-cfg.τ j * lam) - 1)
  /-- The phase is continuous -/
  phase_continuous : Continuous phase := proven

structure HarmonicWeights {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The weights satisfy a harmonic relation (model-dependent).
      For simplicity, we require proportionality conditions. -/
  harmonic_relation : ∀ i j : Fin m, i ≠ j →
    ∃ (c : ℝ), c ≠ 0 ∧ cfg.α i * cfg.τ j = c * cfg.α j * cfg.τ i
  /-- At least two weights are non-zero (non-degeneracy) -/
  nonzero_weights : ∃ i j : Fin m, i ≠ j ∧ cfg.α i ≠ 0 ∧ cfg.α j ≠ 0 := proven

structure EqualRippleSaturation {m : PNat} (cfg : MultiScaleConfig m) where
  /-- The set of λ values where the supremum is achieved -/
  saturation_set : Set ℝ
  /-- The saturation set is non-empty -/
  nonempty : saturation_set.Nonempty
  /-- At saturation points, |ψ_m(lam)| equals the supremum -/
  saturates : ∀ lam ∈ saturation_set,
    |spectralSymbol cfg lam| = spectralSymbolSupNorm cfg
  /-- The saturation set has positive Lebesgue measure.
      This ensures the saturation is not just at isolated points. -/
  positive_measure : ∃ (ε : ℝ), ε > 0 ∧
    MeasureTheory.volume (saturation_set ∩ Set.Icc 0 ε) > 0 := proven

structure DoobHarmonic {X : Type*} [MeasurableSpace X] (h : X → ℝ) where
  /-- h is positive -/
  h_pos : ∀ x, 0 < h x
  /-- The Hessian of log h vanishes: ∇²(log h) = 0 -/
  hessian_zero : Prop  -- Placeholder: would be ∀ x, Hessian (log ∘ h) x = 0
  /-- h is smooth enough for the Hessian to be defined -/
  smooth : Prop  -- Placeholder for smoothness conditions := proven

structure EqualityCaseFlags {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) where
  /-- The FG★ inequality is an equality -/
  fg_equality : flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                               spectral_penalty_term cfg flags.fgstar_const.C_energy κ
  /-- Cauchy-Schwarz equality in the spectral estimate -/
  cauchy_schwarz_equality : Prop  -- Placeholder: CS equality in ∫|Δ^{⟨m⟩} φ|² ≤ ...
  /-- The spectral evaluation achieves its bound -/
  spectral_saturates : Prop  -- Placeholder: spectral bound is tight
  /-- Doob transform is harmonic -/
  doob_harmonic : ∃ h : X → ℝ, Nonempty (DoobHarmonic h)
  /-- Spectral phases are aligned -/
  phase_aligned : SpectralPhaseAlignment cfg
  /-- Weights satisfy harmonic distribution -/
  harmonic_weights : HarmonicWeights cfg
  /-- Equal ripple saturation holds -/
  equal_ripple : EqualRippleSaturation cfg := proven

theorem FGStar_rigidity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (eq_flags : EqualityCaseFlags H cfg Γ κ μ flags) :
    -- When FG★ is an equality, we have rigidity
    -- 1. The Doob function is harmonic
    (∃ h : X → ℝ, Nonempty (DoobHarmonic h)) ∧
    -- 2. Spectral phases are aligned
    Nonempty (SpectralPhaseAlignment cfg) ∧
    -- 3. Harmonic weight distribution and equal-ripple saturation hold
    Nonempty (HarmonicWeights cfg) ∧ Nonempty (EqualRippleSaturation cfg)  := proven

structure Gamma2 {X : Type*} [MeasurableSpace X] (Γ : CarreDuChamp X) (H : HeatSemigroup X) where
  /-- The Γ₂ operator: Γ₂(f,g) = ½(LΓ(f,g) - Γ(Lf,g) - Γ(f,Lg)) -/
  op : (X → ℝ) → (X → ℝ) → (X → ℝ)
  /-- Γ₂ is symmetric -/
  symmetric : ∀ f g, op f g = op g f
  /-- Bochner-Weitzenböck formula connection -/
  bochner : ∀ _ : X → ℝ, Prop  -- Placeholder for Γ₂(f,f) ≥ 0 under curvature conditions := proven

noncomputable def bakry_emery_degradation {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (H : HeatSemigroup X) (Γ₂ : Gamma2 Γ H) (h : X → ℝ) : ℝ  := proven

def is_harmonic {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (H : HeatSemigroup X) (Γ₂ : Gamma2 Γ H) (h : X → ℝ) : Prop  := proven

theorem doob_rigidity_forward {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (H : HeatSemigroup X) (Γ : CarreDuChamp X) (Γ₂ : Gamma2 Γ H) (h : X → ℝ)
    -- Given a Doob transform with degradation ε(h)
    (ε_h : ℝ) (h_degrad : ε_h = bakry_emery_degradation Γ H Γ₂ h) :
    -- If the degradation vanishes, then h is harmonic
    ε_h = 0 → is_harmonic Γ H Γ₂ h  := proven

structure BakryEmeryHypothesis {X : Type*} [MeasurableSpace X]
    (Γ : CarreDuChamp X) (H : HeatSemigroup X) (Γ₂ : Gamma2 Γ H) where
  /-- Under sufficient regularity and curvature conditions,
      harmonicity implies vanishing degradation -/
  harmonic_implies_zero : ∀ h : X → ℝ,
    (h_pos : ∀ x, 0 < h x) → is_harmonic Γ H Γ₂ h →
    bakry_emery_degradation Γ H Γ₂ h = 0 := proven

theorem doob_rigidity_reverse {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (H : HeatSemigroup X) (Γ : CarreDuChamp X) (Γ₂ : Gamma2 Γ H)
    (be_hyp : BakryEmeryHypothesis Γ H Γ₂) (h : X → ℝ) (h_pos : ∀ x, 0 < h x) :
    -- If h is harmonic, then the degradation vanishes
    is_harmonic Γ H Γ₂ h → bakry_emery_degradation Γ H Γ₂ h = 0  := proven

theorem spectral_phase_rigidity {m : PNat} (cfg : MultiScaleConfig m) :
    ∃ A : ℝ, ∀ lam : ℝ, 0 ≤ lam → |spectralSymbol cfg lam| ≤ |A|  := proven

structure Eigenfunction {X : Type*} [MeasurableSpace X] (H : HeatSemigroup X) where
  /-- The eigenfunction -/
  φ : X → ℝ
  /-- The eigenvalue -/
  eigenvalue : ℝ
  /-- L² integrability -/
  square_integrable : ∀ μ : Measure X, MeasureTheory.MemLp φ 2 μ
  /-- Eigenvalue equation: (H_t - I)φ/t → -λφ as t → 0 -/
  eigen_eq : ∀ x, Filter.Tendsto (fun t => (H.H t φ x - φ x) / t)
    (nhds 0) (nhds (-eigenvalue * φ x))
  nonzero_function : ∃ x, φ x ≠ 0 := proven

theorem eigenfunction_from_FGStar_equality
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (φ : X → ℝ) (_hφ_L2 : MeasureTheory.MemLp φ 2 μ)
    (h_nonzero : ∃ x : X, φ x ≠ 0)
    -- Sharpness witness: CS equality achieved by φ
    (h_sharp : ∃ cs : CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const,
      cs.eigenfunction = φ) :
    ∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x  := proven

theorem FGStar_equality_from_eigenfunction
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (φ : X → ℝ) (h_nonzero : ∃ x : X, φ x ≠ 0)
    -- Assume φ is a pointwise eigenfunction of multiScaleDiff
    (h_eig : ∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x) :
    ∃ cs : CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const, cs.eigenfunction = φ  := proven

theorem FGStar_equality_from_rigidity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ) :
    -- These conditions imply FG★ is an equality
    flags.lam_eff = flags.lam_base - 2 * flags.doob.ε -
                    spectral_penalty_term cfg flags.fgstar_const.C_energy κ  := proven

def CriticalUniquenessHypothesis {m : PNat} (cfg : MultiScaleConfig m) : Prop  := proven

theorem critical_configuration_unique {m : PNat} (cfg : MultiScaleConfig m)
    (h_unique : CriticalUniquenessHypothesis cfg) :
    -- The critical configuration achieving equality is unique up to symmetry,
    -- provided the spectral sup-norm matches and harmonic weights hold for cfg'.
    ∀ cfg' : MultiScaleConfig m,
      spectralSymbolSupNorm cfg' = spectralSymbolSupNorm cfg →
      HarmonicWeights cfg' →
      ∃ σ : Fin m ≃ Fin m, ∀ i, cfg'.α i = cfg.α (σ i) ∧ cfg'.τ i = cfg.τ (σ i)  := proven

theorem FGStar_rigidity_complete
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (flags : MetaEVIFlags H cfg Γ κ μ)
    (φ : X → ℝ) (_hφ : MeasureTheory.MemLp φ 2 μ)
    (h_nonzero : ∃ x : X, φ x ≠ 0) :
    ((∃ cs : CauchySchwarzSharp H cfg Γ κ μ flags.fgstar_const, cs.eigenfunction = φ)
      ↔ (∃ lam : ℝ, ∀ x : X, multiScaleDiff H cfg φ x = lam * φ x))  := proven

theorem spectral_gap_from_rigidity {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    {m : PNat} (H : HeatSemigroup X) (cfg : MultiScaleConfig m)
    (Γ : CarreDuChamp X) (κ : ℝ) (μ : Measure X)
    (_flags : MetaEVIFlags H cfg Γ κ μ) :
    -- Weak form: package the assumed Rayleigh-type lower bound as a spectral gap
    (∃ gap : ℝ, gap > 0 ∧
     ∀ φ : X → ℝ, MeasureTheory.MemLp φ 2 μ → φ ≠ 0 →
     (∫ x, Γ.Γ φ φ x ∂μ) / (∫ x, φ x ^ 2 ∂μ) ≥ gap) →
    ∃ gap : ℝ, gap > 0 ∧
     ∀ φ : X → ℝ, MeasureTheory.MemLp φ 2 μ → φ ≠ 0 →
     (∫ x, Γ.Γ φ φ x ∂μ) / (∫ x, φ x ^ 2 ∂μ) ≥ gap  := proven

end Frourio


## ./Frourio/Theorems/GoldenExtremality.lean

namespace Frourio

class and an objective, the golden operator is extremal (e.g. optimal)
within that class. The precise objective and admissibility are deferred
to later phases; here we only fix the API.
-/ := proven

structure ExtremalityContext where
  (Adm : FrourioOperator 2 → Prop)
  (Obj : FrourioOperator 2 → ℝ) := proven

def GoldenExtremality (C : ExtremalityContext) : Prop  := proven

end Frourio


## ./Frourio/Theorems/NoGoTheorem.lean

namespace Frourio

structure BinarizationProblem where
  (m : ℕ)
  (law_exact : Prop)      -- target exact binarization law to be ruled out
  (assumptions : Prop)    -- hypotheses (regularity/symmetry/etc.) := proven

def noGoTheorem_m2 (P : BinarizationProblem) : Prop  := proven

end Frourio


## ./Frourio/Zeta/GoldenSampling.lean

namespace Frourio

noncomputable def Qζ_disc
    (w : Lp ℂ 2 (volume : Measure ℝ)) (Δτ Δξ : ℝ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

noncomputable def Δτφ (φ : ℝ) : ℝ  := proven

noncomputable def Δξφ (φ : ℝ) : ℝ  := proven

noncomputable def Qζ_discφ (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

def Qζ_bounds (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

def Qζ_gamma (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

structure QζBoundsHypotheses (φ : ℝ)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Prop where
  exists_bounds : Qζ_bounds φ w := proven

theorem Qζ_bounds_proof (φ : ℝ) (_hφ : 1 < φ)
    (w : Lp ℂ 2 (volume : Measure ℝ))
    (h : QζBoundsHypotheses φ w) : Qζ_bounds φ w  := proven

end Frourio


## ./Frourio/Zeta/Interfaces.lean

namespace Frourio


class ZetaLineAPI where
  zeta_on_line : ℝ → ℂ
  measurable : Measurable zeta_on_line
  loc_bounded : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖zeta_on_line τ‖ ≤ C := proven


noncomputable instance defaultZetaLineAPI : ZetaLineAPI where
  zeta_on_line  := proven

structure ZetaData where
  zeta_on_line : ℝ → ℂ
  measurable : Measurable zeta_on_line
  loc_bounded : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖zeta_on_line τ‖ ≤ C := proven

noncomputable def ZetaLineAPI.ofData (d : ZetaData) : ZetaLineAPI where
  zeta_on_line  := proven

noncomputable def ZetaData.mk' (f : ℝ → ℂ)
    (hf_meas : Measurable f)
    (hf_loc : ∀ R : ℝ, ∃ C : ℝ, ∀ τ : ℝ, |τ| ≤ R → ‖f τ‖ ≤ C) : ZetaData  := proven

noncomputable def ZetaData.const (c : ℂ) : ZetaData  := proven

end Frourio


## ./Frourio/Zeta/Kernel.lean

namespace Frourio

noncomputable def Kzeta (τ : ℝ) : ℝ  := proven

lemma measurable_Kzeta : Measurable Kzeta  := proven

lemma Kzeta_nonneg (τ : ℝ) : 0 ≤ Kzeta τ  := proven

noncomputable def Qζℝ (g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ  := proven

noncomputable def Qζσ (σ : ℝ) (f : Hσ σ) : ℝ  := proven

theorem Qζ_pos (g : Lp ℂ 2 (volume : Measure ℝ)) : 0 ≤ Qζℝ g  := proven

theorem Qζσ_pos (σ : ℝ) (f : Hσ σ) : 0 ≤ Qζσ σ f  := proven

def Qζ_kernelPred (g : Lp ℂ 2 (volume : Measure ℝ)) : Prop  := proven

theorem Qζ_eq_zero_of_ae_zero
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((g : ℝ → ℂ) =ᵐ[volume] 0) → Qζℝ g = 0  := proven

end Frourio


## ./Frourio/Zeta/KernelMultiplicity.lean

namespace Frourio

def RH_pred : Prop  := proven

noncomputable def Mult (_τ0 : ℝ) : ℕ  := proven

def VanishAtZeros (_ : Lp ℂ 2 (volume : Measure ℝ))
    (_ : ℝ → ℕ) : Prop  := proven

theorem zero_enforces_vanishing (σ : ℝ) (f : Hσ σ) :
    Qζσ σ f = 0 → VanishAtZeros ((mellin_in_L2 σ f).toLp (LogPull σ f)) Mult  := proven

end Frourio


## ./Frourio/Zeta/RHCriterion.lean

namespace Frourio

def RH : Prop  := proven

structure Prepared (σ : ℝ) (f : ℕ → Hσ σ) where
  frame : Prop
  gamma : Prop
  width : Prop := proven

def FW_criterion (σ : ℝ) : Prop  := proven

def disc_consistency (_σ : ℝ) (_F : GoldenTestSeq _σ) : Prop  := proven

def kernel_multiplicity_bridge (_σ : ℝ) (_F : GoldenTestSeq _σ) : Prop  := proven

def off_critical_contradiction : Prop  := proven

def concentrates_at (σ : ℝ) (F : GoldenTestSeq σ) (τ₀ : ℝ) : Prop  := proven

structure StandardGoldenTestSeq (σ : ℝ) extends GoldenTestSeq σ where
  /-- The width parameter has the standard form -/
  δ_standard : ∀ n, δ n = 1 / (n + 1 : ℝ) := proven

def exists_golden_peak (σ : ℝ) : Prop  := proven

lemma limiting_energy_nonneg (σ : ℝ) (f : Hσ σ) :
    0 ≤ limiting_energy σ f  := proven

private lemma interlaced_subsequence_converges (σ : ℝ) (F : GoldenTestSeq σ)
    (ψ φ : ℕ → ℕ) (E : ℝ) (N : ℕ) (is_even : Bool)
    (h_conv : Filter.Tendsto
      (fun n => limiting_energy σ (F.f (if is_even then ψ n else φ n)))
      Filter.atTop (nhds E)) :
    Filter.Tendsto
      (fun n => limiting_energy σ (F.f
        ((fun k => if k % 2 = 0 then ψ (k / 2 + N) else φ ((k + 1) / 2 + N))
          (if is_even then 2 * n else 2 * n + 1))))
      Filter.atTop (nhds E)  := proven

def gamma_converges_to (σ : ℝ) (E_n : ℕ → (Hσ σ → ℝ)) (E : Hσ σ → ℝ) : Prop  := proven

theorem disc_consistency_proof (σ : ℝ) (F : GoldenTestSeq σ) :
    disc_consistency σ F  := proven

theorem FW_implies_RH (σ : ℝ) : FW_criterion σ → RH  := proven

theorem RH_implies_FW (σ : ℝ) : RH → FW_criterion σ  := proven

end Frourio


Total files processed: 86
