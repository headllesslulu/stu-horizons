import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Topology.Order.IntermediateValue

/-!
# Entropy superadditivity for rotating four-electric-charge STU horizons

Units and normalization are those of Cvetič, Gibbons, Lü and Pope,
Phys. Rev. D 98 (2018), equations (3.75)–(3.80). The internal charge
coordinate is qᵢ = 4 Qᵢ. The public theorem uses the physical Qᵢ.
-/

noncomputable section
open Real Set
namespace STUHorizons

abbrev Four := Fin 4 → ℝ

def sum4 (x : Four) : ℝ := x 0 + x 1 + x 2 + x 3
def prod4 (x : Four) : ℝ := (x 0*x 1)*(x 2*x 3)

private theorem prod_nonneg (x : Four) (h : ∀ i, 0 ≤ x i) : 0 ≤ prod4 x :=
  mul_nonneg (mul_nonneg (h 0) (h 1)) (mul_nonneg (h 2) (h 3))

private theorem prod_mono {x y : Four} (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ y i) :
    prod4 x ≤ prod4 y := by
  unfold prod4
  apply mul_le_mul (mul_le_mul (h 0) (h 1) (hx 1) ((hx 0).trans (h 0)))
    (mul_le_mul (h 2) (h 3) (hx 3) ((hx 2).trans (h 2)))
    (mul_nonneg (hx 2) (hx 3)) (mul_nonneg ((hx 0).trans (h 0)) ((hx 1).trans (h 1)))

private theorem prod_mul (x y : Four) :
    prod4 (fun i => x i*y i) = prod4 x*prod4 y := by unfold prod4; ring

private theorem prod_sq (x : Four) : prod4 (fun i => (x i)^2) = (prod4 x)^2 := by
  unfold prod4; ring

private theorem sum_mono {x y : Four} (h : ∀ i, x i ≤ y i) : sum4 x ≤ sum4 y :=
  add_le_add (add_le_add (add_le_add (h 0) (h 1)) (h 2)) (h 3)

private theorem sum_add (x y : Four) : sum4 (x+y) = sum4 x+sum4 y := by
  simp only [sum4, Pi.add_apply]; ring

/-- A common nonextremality parameter m sets the four equilibrium energies. -/
def energy (m : ℝ) (q : Four) : Four := fun i => √(m^2+(q i)^2)
def mass (m : ℝ) (q : Four) : ℝ := sum4 (energy m q)/4
def Feasible (e q : Four) := ∀ i, |q i| ≤ e i

theorem energy_feasible (m : ℝ) (q : Four) : Feasible (energy m q) q := by
  intro i
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg m])

private theorem energy_sq (m : ℝ) (q : Four) (i : Fin 4) :
    (energy m q i)^2 = m^2 + (q i)^2 := Real.sq_sqrt (by positivity)

private theorem mass_continuous (q : Four) : Continuous (fun m => mass m q) := by
  unfold mass sum4 energy
  fun_prop

theorem mass_strict {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (q : Four) :
    mass a q < mass b q := by
  have hs : a^2<b^2 := by nlinarith [mul_pos (sub_pos.mpr hab) (show 0<a+b by linarith)]
  have h (i : Fin 4) : energy a q i < energy b q i :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  unfold mass sum4
  linarith [h 0,h 1,h 2,h 3]

theorem exists_unique_seed {M : ℝ} {q : Four} (hM : mass 0 q ≤ M) :
    ∃! m : ℝ, 0 ≤ m ∧ mass m q = M := by
  have hbase : 0 ≤ mass 0 q := by
    unfold mass sum4 energy
    positivity
  have hp := hbase.trans hM
  have he (i : Fin 4) : M ≤ energy M q i := by
    calc M = √(M^2) := (Real.sqrt_sq hp).symm
         _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (q i)])
  have ht : M ≤ mass M q := by unfold mass sum4; linarith [he 0,he 1,he 2,he 3]
  obtain ⟨m,hm,hmM⟩ := intermediate_value_Icc hp (mass_continuous q).continuousOn
    (show M ∈ Icc (mass 0 q) (mass M q) from ⟨hM,ht⟩)
  refine ⟨m,⟨hm.1,hmM⟩,?_⟩
  rintro n ⟨hn,hnM⟩
  rcases lt_trichotomy n m with hl|heq|hr
  · linarith [mass_strict hn hl q]
  · exact heq
  · linarith [mass_strict hm.1 hr q]

/-- The unique physical seed. The default 0 is never used on the admissible domain. -/
def seed (M : ℝ) (q : Four) : ℝ :=
  if h : mass 0 q ≤ M then (exists_unique_seed h).exists.choose else 0

theorem seed_spec {M : ℝ} {q : Four} (h : mass 0 q ≤ M) :
    0 ≤ seed M q ∧ mass (seed M q) q = M := by
  simpa [seed,h] using (exists_unique_seed h).exists.choose_spec

def upper (e q : ℝ) := (√(e+q)+√(e-q))/2
def lower (e q : ℝ) := (√(e+q)-√(e-q))/2
def upperProduct (e q : Four) := prod4 (fun i => upper (e i) (q i))
def lowerProduct (e q : Four) := prod4 (fun i => lower (e i) (q i))
def leftSector (e q : Four) := upperProduct e q + lowerProduct e q
def rightSector (e q : Four) := upperProduct e q - lowerProduct e q

private theorem upper_nonneg (e q : ℝ) : 0 ≤ upper e q := by unfold upper; positivity
private theorem lower_abs (e q : ℝ) : |lower e q| ≤ upper e q := by
  unfold lower upper
  exact abs_le.mpr ⟨by linarith [Real.sqrt_nonneg (e+q)],by linarith [Real.sqrt_nonneg (e-q)]⟩

private theorem products_bound (e q : Four) : |lowerProduct e q| ≤ upperProduct e q := by
  have he : |lowerProduct e q| = prod4 (fun i => |lower (e i) (q i)|) := by
    simp only [lowerProduct,prod4,abs_mul]
  rw [he]
  exact prod_mono (fun _ => abs_nonneg _) (fun _ => lower_abs ..)

private theorem root_terms {e q : ℝ} (h : |q| ≤ e) : 0 ≤ e+q ∧ 0 ≤ e-q := by
  have := abs_le.mp h
  constructor <;> linarith

private theorem upper_lower {e q : ℝ} (h : |q| ≤ e) :
    upper e q * lower e q = q/2 := by
  obtain ⟨hp,hn⟩ := root_terms h
  unfold upper lower
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hn]

private theorem upper_square {e q : ℝ} (h : |q| ≤ e) :
    (upper e q)^2 = (e+√(e^2-q^2))/2 := by
  obtain ⟨hp,hn⟩ := root_terms h
  have hmul : √(e+q)*√(e-q)=√(e^2-q^2) := by
    rw [← Real.sqrt_mul hp]
    congr 1
    ring
  unfold upper
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hn]

private theorem product_invariant {e q : Four} (h : Feasible e q) :
    upperProduct e q * lowerProduct e q = prod4 (fun i => q i/2) := by
  unfold upperProduct lowerProduct
  rw [← prod_mul]
  exact congrArg prod4 (funext (fun i => upper_lower (h i)))

/-- Four nonnegative numbers with sum at most four have product at most one. -/
private theorem amgm_four (x : Four) (hx : ∀ i, 0 ≤ x i) (hs : sum4 x ≤ 4) :
    prod4 x ≤ 1 := by
  let a := (x 0+x 1)/2
  let b := (x 2+x 3)/2
  have ha : 0≤a := by dsimp [a]; linarith [hx 0,hx 1]
  have hb : 0≤b := by dsimp [b]; linarith [hx 2,hx 3]
  have hab : a+b≤2 := by unfold sum4 at hs; dsimp [a,b]; linarith
  have hx01 : x 0*x 1≤a^2 := by dsimp [a]; nlinarith [sq_nonneg (x 0-x 1)]
  have hx23 : x 2*x 3≤b^2 := by dsimp [b]; nlinarith [sq_nonneg (x 2-x 3)]
  have hp : a*b≤1 := by nlinarith [sq_nonneg (a-b),mul_nonneg (by linarith : 0≤2-(a+b)) (by linarith : 0≤2+(a+b))]
  calc prod4 x ≤ a^2*b^2 := mul_le_mul hx01 hx23 (mul_nonneg (hx 2) (hx 3)) (sq_nonneg _)
       _ = (a*b)^2 := (mul_pow ..).symm
       _ ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0≤1-a*b) (by nlinarith [mul_nonneg ha hb] : 0≤1+a*b)]

/-- A supporting inequality for a single charge slot, including e=|q|. -/
private theorem single_support {m E e q : ℝ} (hm : 0 < m) (he : |q| ≤ e)
    (hE : |q| ≤ E) (hE2 : E^2=m^2+q^2) :
    (upper e q)^2 ≤ (upper E q)^2*(1+(e-E)/m) := by
  have hE0 := (abs_nonneg q).trans hE
  have he0 := (abs_nonneg q).trans he
  have hey : q^2 ≤ E*e := by
    calc q^2 = |q| * |q| := by simp only [← pow_two,sq_abs]
         _ ≤ _ := mul_le_mul hE he (abs_nonneg _) hE0
  have hd : 0≤e^2-q^2 := by
    have := mul_nonneg (root_terms he).1 (root_terms he).2
    nlinarith
  have hroot : m*√(e^2-q^2) ≤ E*e-q^2 := by
    apply le_of_sq_le_sq _ (sub_nonneg.mpr hey)
    rw [mul_pow,Real.sq_sqrt hd]
    nlinarith only [sq_nonneg (q*(e-E)),show (E^2-m^2-q^2)*e^2=0 by rw [hE2]; ring,
      show (E^2-m^2-q^2)*q^2=0 by rw [hE2]; ring]
  have hdiff : E^2-q^2=m^2 := by linarith
  rw [upper_square he,upper_square hE,hdiff,Real.sqrt_sq hm.le]
  apply (le_of_sub_nonneg ?_)
  field_simp
  nlinarith [hE2,hroot]

private theorem sum_eq_of_order {f g : Four} (h : ∀ i, f i ≤ g i) (hs : sum4 f=sum4 g) :
    f=g := by
  funext i
  unfold sum4 at hs
  fin_cases i
  · change f 0=g 0; linarith [h 0,h 1,h 2,h 3]
  · change f 1=g 1; linarith [h 0,h 1,h 2,h 3]
  · change f 2=g 2; linarith [h 0,h 1,h 2,h 3]
  · change f 3=g 3; linarith [h 0,h 1,h 2,h 3]

/-- Equilibrium maximizes the product of the four upper amplitudes at fixed
total energy and fixed individual charges. -/
theorem upper_maximizes {m : ℝ} (hm : 0 ≤ m) (q e : Four) (hf : Feasible e q)
    (hs : sum4 e = sum4 (energy m q)) :
    upperProduct e q ≤ upperProduct (energy m q) q := by
  rcases hm.eq_or_lt with hz|hp
  · subst m
    have h (i : Fin 4) : energy 0 q i ≤ e i := by simpa [energy,Real.sqrt_sq_eq_abs] using hf i
    rw [sum_eq_of_order h hs.symm]
  · let E := energy m q
    let w (i : Fin 4) := 1+(e i-E i)/m
    have hsingle (i) : (upper (e i) (q i))^2 ≤ (upper (E i) (q i))^2*w i :=
      single_support hp (hf i) (energy_feasible m q i) (energy_sq m q i)
    have hw (i : Fin 4) : 0 ≤ w i := by
      by_contra! h
      have hpos : 0 < upper (E i) (q i) := by
        have hsq : (q i)^2 < (E i)^2 := by
          have := energy_sq m q i
          change (E i)^2=_ at this
          nlinarith [sq_pos_of_pos hp]
        have hg : |q i|<E i := by
          have := energy_feasible m q i
          by_contra! hc
          have ee := le_antisymm hc this
          rw [ee,sq_abs] at hsq
          exact (lt_irrefl _ hsq)
        unfold upper
        have hsum : 0<E i+q i := by have := abs_lt.mp hg; linarith
        positivity
      have := mul_neg_of_pos_of_neg (sq_pos_of_pos hpos) h
      linarith [hsingle i,sq_nonneg (upper (e i) (q i))]
    have hwSum : sum4 w = 4 := by
      change sum4 e = sum4 E at hs
      unfold sum4 at hs ⊢
      simp only [w]
      field_simp
      linarith
    have hprod := prod_mono (fun i => sq_nonneg (upper (e i) (q i))) hsingle
    rw [prod_sq,prod_mul,prod_sq] at hprod
    apply le_of_sq_le_sq _ (prod_nonneg _ (fun _ => upper_nonneg ..))
    exact hprod.trans (mul_le_of_le_one_right (sq_nonneg _) (amgm_four w hw hwSum.le))

private theorem sector_monotone {a b A B : ℝ} (ha : |b|≤a) (hA : |B|≤A)
    (hle : a≤A) (hinv : a*b=A*B) :
    a+b≤A+B ∧ a-b≤A-B := by
  have ha0 := (abs_nonneg b).trans ha
  have hA0 := (abs_nonneg B).trans hA
  rcases hA0.eq_or_lt with hz|hp
  · have ha' : a=0 := by linarith
    have hb := abs_le.mp ha
    have hB := abs_le.mp hA
    constructor <;> linarith
  · have hb := abs_le.mp (ha.trans hle)
    constructor
    · apply (mul_le_mul_iff_of_pos_left hp).mp
      nlinarith only [hinv,mul_nonneg (sub_nonneg.mpr hle) (show 0≤A-b by linarith)]
    · apply (mul_le_mul_iff_of_pos_left hp).mp
      nlinarith only [hinv,mul_nonneg (sub_nonneg.mpr hle) (show 0≤A+b by linarith)]

theorem sectors_maximize {m : ℝ} (hm : 0 ≤ m) (q e : Four) (hf : Feasible e q)
    (hs : sum4 e = sum4 (energy m q)) :
    leftSector e q ≤ leftSector (energy m q) q ∧ rightSector e q ≤ rightSector (energy m q) q :=
  sector_monotone (products_bound e q) (products_bound _ q) (upper_maximizes hm q e hf hs)
    ((product_invariant hf).trans (product_invariant (energy_feasible m q)).symm)

private theorem root_pair {x y u v : ℝ} (hx : 0≤x) (hy : 0≤y) (hu : 0≤u) (hv : 0≤v) :
    √x*√y + √u*√v ≤ √(x+u)*√(y+v) := by
  have hcross : 0≤x*v+u*y-2*(√x*√y)*(√u*√v) := by
    have h := sq_nonneg (√x*√v - √u*√y)
    rw [sub_sq,mul_pow,mul_pow,Real.sq_sqrt hx,Real.sq_sqrt hv,Real.sq_sqrt hu,Real.sq_sqrt hy] at h
    linarith only [h]
  apply le_of_sq_le_sq _ (by positivity)
  rw [add_sq,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hx,Real.sq_sqrt hy,Real.sq_sqrt hu,
    Real.sq_sqrt hv,Real.sq_sqrt (add_nonneg hx hu),Real.sq_sqrt (add_nonneg hy hv)]
  linarith only [hcross]

private theorem product_super {a b c d A B : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hc : 0≤c) (hd : 0≤d) (hA : a+c≤A) (hB : b+d≤B) :
    a*b+c*d ≤ A*B := by
  calc a*b+c*d ≤ (a+c)*(b+d) := by nlinarith only [mul_nonneg ha hd,mul_nonneg hc hb]
       _ ≤ A*B := mul_le_mul hA hB (add_nonneg hb hd) ((add_nonneg ha hc).trans hA)

/-- The paired square-root terms expose the positive coefficients in each sector. -/
private def rootEntry (e q : Four) (i : Fin 4) (s : Bool) : ℝ :=
  if s then e i + q i else e i - q i
private def pair (e q : Four) (i j : Fin 4) (s : Bool) : ℝ :=
  (√(rootEntry e q i true)*√(rootEntry e q j s) +
   √(rootEntry e q i false)*√(rootEntry e q j (!s)))/2

private theorem entry_nonneg {e q : Four} (hf : Feasible e q) (i : Fin 4) (s : Bool) :
    0 ≤ rootEntry e q i s := by
  cases s
  · exact (root_terms (hf i)).2
  · exact (root_terms (hf i)).1

private theorem entry_add (a q b p : Four) (i : Fin 4) (s : Bool) :
    rootEntry (a+b) (q+p) i s = rootEntry a q i s + rootEntry b p i s := by
  cases s <;> simp [rootEntry] <;> ring

private theorem pair_nonneg (a q : Four) (i j : Fin 4) (s : Bool) :
    0 ≤ pair a q i j s := by unfold pair; positivity

private theorem pair_super {a q b p : Four} (ha : Feasible a q) (hb : Feasible b p)
    (i j : Fin 4) (s : Bool) :
    pair a q i j s + pair b p i j s ≤ pair (a+b) (q+p) i j s := by
  have h (s t : Bool) := root_pair (entry_nonneg ha i s) (entry_nonneg ha j t)
    (entry_nonneg hb i s) (entry_nonneg hb j t)
  unfold pair
  simp only [entry_add]
  linarith [h true s,h false (!s)]

private theorem parity_identity (e q : Four) :
    leftSector e q =
      (pair e q 0 1 true * pair e q 2 3 true + pair e q 0 1 false * pair e q 2 3 false)/2 ∧
    rightSector e q =
      (pair e q 0 1 true * pair e q 2 3 false + pair e q 0 1 false * pair e q 2 3 true)/2 := by
  constructor <;>
    simp only [leftSector,rightSector,upperProduct,lowerProduct,prod4,upper,lower,pair,rootEntry,
      Bool.not_true,Bool.not_false,ite_true,Bool.false_eq_true,ite_false] <;> ring

/-- Both sectors increase superadditively under coordinatewise pooling,
before allowing the four energies to re-equilibrate. -/
theorem pooled_sectors {a q b p : Four} (ha : Feasible a q) (hb : Feasible b p) :
    leftSector a q + leftSector b p ≤ leftSector (a+b) (q+p) ∧
    rightSector a q + rightSector b p ≤ rightSector (a+b) (q+p) := by
  have h (s t : Bool) := product_super (pair_nonneg a q 0 1 s) (pair_nonneg a q 2 3 t)
    (pair_nonneg b p 0 1 s) (pair_nonneg b p 2 3 t) (pair_super ha hb 0 1 s) (pair_super ha hb 2 3 t)
  constructor
  · simp only [(parity_identity _ _).1]; linarith [h true true,h false false]
  · simp only [(parity_identity _ _).2]; linarith [h true false,h false true]

/-- On equilibrium data, the product of the two signed entries is m². -/
private theorem root_complement {m : ℝ} (hm : 0≤m) (q : Four) (i : Fin 4) (s : Bool) :
    √(rootEntry (energy m q) q i s)*√(rootEntry (energy m q) q i (!s))=m := by
  rw [← Real.sqrt_mul (entry_nonneg (energy_feasible m q) i s)]
  have he : rootEntry (energy m q) q i s * rootEntry (energy m q) q i (!s) = m^2 := by
    cases s <;> simp [rootEntry] <;> nlinarith [energy_sq m q i]
  rw [he,Real.sqrt_sq hm]

private theorem pair_floor {m : ℝ} (hm : 0≤m) (q : Four) (i j : Fin 4) (s : Bool) :
    m ≤ pair (energy m q) q i j s := by
  let r (k : Fin 4) (b : Bool) := √(rootEntry (energy m q) q k b)
  let x := r i true * r j s
  let y := r i false * r j (!s)
  have hxy : x*y=m^2 := by
    calc x*y = (r i true * r i false)*(r j s * r j (!s)) := by dsimp only [x,y]; ring
         _ = m^2 := by
           change (√_ * √_)*(√_ * √_)=_
           have hi := root_complement hm q i true
           simp only [Bool.not_true] at hi
           rw [hi,root_complement hm q j s,pow_two]
  have hx : 0≤x := by dsimp [x,r]; positivity
  have hy : 0≤y := by dsimp [y,r]; positivity
  change m≤(x+y)/2
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith only [hxy,sq_nonneg (x-y)]

/-- Each equilibrium sector has a cross term of at least 2mn when two states
with nonextremality parameters m and n are pooled. -/
theorem pooled_gain {m n : ℝ} (hm : 0≤m) (hn : 0≤n) (q p : Four) :
    let a := energy m q
    let b := energy n p
    (leftSector a q + leftSector b p + 2*m*n ≤ leftSector (a+b) (q+p)) ∧
    (rightSector a q + rightSector b p + 2*m*n ≤ rightSector (a+b) (q+p)) := by
  dsimp only
  let a := energy m q
  let b := energy n p
  have hprod (s t : Bool) :
      pair a q 0 1 s * pair a q 2 3 t + pair b p 0 1 s * pair b p 2 3 t + 2*m*n ≤
        pair (a+b) (q+p) 0 1 s * pair (a+b) (q+p) 2 3 t := by
    have h12 := pair_super (energy_feasible m q) (energy_feasible n p) 0 1 s
    have h34 := pair_super (energy_feasible m q) (energy_feasible n p) 2 3 t
    have hac : m*n≤pair a q 0 1 s * pair b p 2 3 t :=
      mul_le_mul (pair_floor hm q 0 1 s) (pair_floor hn p 2 3 t) hn (pair_nonneg ..)
    have hbc : n*m≤pair b p 0 1 s * pair a q 2 3 t :=
      mul_le_mul (pair_floor hn p 0 1 s) (pair_floor hm q 2 3 t) hm (pair_nonneg ..)
    calc _ ≤ (pair a q 0 1 s + pair b p 0 1 s)*(pair a q 2 3 t + pair b p 2 3 t) := by
               nlinarith only [hac,hbc]
         _ ≤ _ := mul_le_mul h12 h34 (add_nonneg (pair_nonneg ..) (pair_nonneg ..)) (pair_nonneg ..)
  change (_ + _ + _ ≤ leftSector (a+b) (q+p)) ∧ (_ + _ + _ ≤ rightSector (a+b) (q+p))
  constructor
  · simp only [(parity_identity _ _).1]
    linarith [hprod true true,hprod false false]
  · simp only [(parity_identity _ _).2]
    linarith [hprod true false,hprod false true]

private theorem feasible_add {a q b p : Four} (ha : Feasible a q) (hb : Feasible b p) :
    Feasible (a+b) (q+p) := fun i => (abs_add_le (q i) (p i)).trans (add_le_add (ha i) (hb i))

private theorem zero_mass_subadd (p q : Four) : mass 0 (p+q) ≤ mass 0 p+mass 0 q := by
  have h := sum_mono (fun i : Fin 4 => abs_add_le (p i) (q i))
  unfold mass sum4 at ⊢
  simp only [energy,zero_pow (by decide : 2≠0),zero_add,Real.sqrt_sq_eq_abs,Pi.add_apply]
  unfold sum4 at h
  linarith

def spinNorm (R J : ℝ) : ℝ := √(R^2-J^2)

private theorem spin_split {R J : ℝ} (h : |J|≤R) : spinNorm R J=√(R+J)*√(R-J) := by
  rw [← Real.sqrt_mul (root_terms h).1]
  unfold spinNorm
  congr 1
  ring

private theorem spin_super {R S J K : ℝ} (h : |J|≤R) (k : |K|≤S) :
    spinNorm R J + spinNorm S K ≤ spinNorm (R+S) (J+K) := by
  have hk := (abs_add_le J K).trans (add_le_add h k)
  rw [spin_split h,spin_split k,spin_split hk]
  convert root_pair (root_terms h).1 (root_terms h).2 (root_terms k).1 (root_terms k).2 using 1
  ring_nf

private theorem spin_mono {R S J : ℝ} (h : |J|≤R) (hRS : R≤S) :
    spinNorm R J ≤ spinNorm S J := by
  apply Real.sqrt_le_sqrt
  have hR := (abs_nonneg J).trans h
  nlinarith [mul_nonneg (sub_nonneg.mpr hRS) (show 0≤S+R by linarith)]

/-- A state is labelled only by its ADM mass, angular momentum and the four
physical electric charges, normalized as in the paper's equation (3.75). -/
@[ext] structure State where
  M : ℝ
  J : ℝ
  Q : Four

instance : Add State := ⟨fun x y => ⟨x.M+y.M,x.J+y.J,x.Q+y.Q⟩⟩

def State.q (x : State) : Four := fun i => 4*x.Q i
def State.m (x : State) : ℝ := seed x.M x.q
def State.e (x : State) : Four := energy x.m x.q
def State.L (x : State) : ℝ := leftSector x.e x.q
def State.R (x : State) : ℝ := rightSector x.e x.q
def State.Admissible (x : State) := mass 0 x.q ≤ x.M ∧ |x.J| ≤ x.R
def State.entropy (x : State) : ℝ := 2*Real.pi*(x.L + spinNorm x.R x.J)

private theorem charge_add (x y : State) : (x+y).q=x.q+y.q := by
  funext i
  change 4*(x.Q i+y.Q i)=4*x.Q i+4*y.Q i
  ring

/-- The sum state exists on the physical branch. Each of its two sector
parameters dominates the sum of the inputs by at least 2m₁m₂. -/
theorem merged_sectors {x y : State} (hx : x.Admissible) (hy : y.Admissible) :
    (x+y).Admissible ∧ x.L+y.L+2*x.m*y.m≤(x+y).L ∧ x.R+y.R+2*x.m*y.m≤(x+y).R := by
  have hq := charge_add x y
  have hM : mass 0 (x+y).q ≤ (x+y).M := by
    rw [hq]
    exact (zero_mass_subadd _ _).trans (add_le_add hx.1 hy.1)
  obtain ⟨hmx,hEx⟩ := seed_spec hx.1
  obtain ⟨hmy,hEy⟩ := seed_spec hy.1
  obtain ⟨hm,hE⟩ := seed_spec hM
  change 0≤x.m at hmx
  change 0≤y.m at hmy
  change 0≤(x+y).m at hm
  change sum4 x.e/4=x.M at hEx
  change sum4 y.e/4=y.M at hEy
  change sum4 (x+y).e/4=x.M+y.M at hE
  have hsum : sum4 (x.e+y.e)=sum4 (x+y).e := by rw [sum_add]; linarith
  have hf : Feasible (x.e+y.e) (x+y).q := by
    rw [hq]; exact feasible_add (energy_feasible x.m x.q) (energy_feasible y.m y.q)
  have hopt := sectors_maximize hm (x+y).q (x.e+y.e) hf hsum
  have hg := pooled_gain hmx hmy x.q y.q
  change (_ ≤ leftSector (x.e+y.e) (x.q+y.q)) ∧ (_ ≤ rightSector (x.e+y.e) (x.q+y.q)) at hg
  rw [← hq] at hg
  have hl := hg.1.trans hopt.1
  have hr := hg.2.trans hopt.2
  change x.R+y.R+2*x.m*y.m≤(x+y).R at hr
  have hs : |x.J+y.J|≤x.R+y.R := (abs_add_le ..).trans (add_le_add hx.2 hy.2)
  exact ⟨⟨hM,hs.trans ((le_add_of_nonneg_right (by positivity)).trans hr)⟩,hl,hr⟩

/-- The outer horizon entropy satisfies the sharp quantitative inequality.
There are no charge equalities, a common charge ratio, or aligned-spin assumptions. -/
theorem entropy_gap {x y : State} (hx : x.Admissible) (hy : y.Admissible) :
    x.entropy + y.entropy + 8*Real.pi*x.m*y.m ≤ (x+y).entropy := by
  obtain ⟨_,hl,hr⟩ := merged_sectors hx hy
  have hd : 0≤2*x.m*y.m := by
    have hx0 : 0≤x.m := (seed_spec hx.1).1
    have hy0 : 0≤y.m := (seed_spec hy.1).1
    positivity
  let d := 2*x.m*y.m
  have h0 : |(0:ℝ)|≤d := by simpa [d] using hd
  have h := (abs_add_le x.J y.J).trans (add_le_add hx.2 hy.2)
  have hh := spin_super h h0
  have hz : spinNorm d 0=d := by simp [spinNorm,Real.sqrt_sq hd,d]
  rw [add_zero,hz] at hh
  have hlim := spin_mono (h.trans (le_add_of_nonneg_right hd)) hr
  have hs := (add_le_add (spin_super hx.2 hy.2) (le_refl d)).trans (hh.trans hlim)
  change spinNorm x.R x.J + spinNorm y.R y.J + 2*x.m*y.m ≤ spinNorm (x+y).R (x.J+y.J) at hs
  change 2*Real.pi*(x.L+spinNorm x.R x.J)+2*Real.pi*(y.L+spinNorm y.R y.J)+_ ≤
    2*Real.pi*((x+y).L+spinNorm (x+y).R (x.J+y.J))
  have hi := mul_le_mul_of_nonneg_left (add_le_add hl hs) (by positivity : 0≤2*Real.pi)
  linarith only [hi]

/-- The full four-charge superadditivity question in §6 of Cvetič–Gibbons–Lü–Pope.
Admissibility of the combined physical data is a conclusion. -/
theorem four_charge_superadditivity {x y : State} (hx : x.Admissible) (hy : y.Admissible) :
    (x+y).Admissible ∧ x.entropy+y.entropy≤(x+y).entropy := by
  have hx0 : 0≤x.m := (seed_spec hx.1).1
  have hy0 : 0≤y.m := (seed_spec hy.1).1
  exact ⟨(merged_sectors hx hy).1,(le_add_of_nonneg_right (by positivity)).trans (entropy_gap hx hy)⟩

/-- The charge-dependent seed is recovered from the physical mass. -/
theorem seed_of_mass {m : ℝ} (hm : 0 ≤ m) (q : Four) : seed (mass m q) q = m := by
  have h0 : mass 0 q ≤ mass m q := by
    rcases hm.eq_or_lt with hz|hp
    · rw [hz]
    · exact (mass_strict le_rfl hp q).le
  exact (exists_unique_seed h0).unique (seed_spec h0) ⟨hm,rfl⟩

def coshProduct (δ : Four) := prod4 (fun i => Real.cosh (δ i))
def sinhProduct (δ : Four) := prod4 (fun i => Real.sinh (δ i))

/-- The original Cvetič–Gibbons–Lü–Pope mass, spin and charges (3.75). -/
def fromBoost (m a : ℝ) (δ : Four) : State :=
  ⟨sum4 (fun i => m * Real.cosh (2*δ i))/4, m*a*(coshProduct δ-sinhProduct δ),
    fun i => m * Real.sinh (2*δ i)/4⟩

private theorem boost_q (m a : ℝ) (δ : Four) (i : Fin 4) :
    (fromBoost m a δ).q i = m * Real.sinh (2*δ i) := by
  unfold State.q fromBoost
  dsimp
  ring

private theorem boost_energy {m : ℝ} (hm : 0≤m) (a : ℝ) (δ : Four) :
    energy m (fromBoost m a δ).q = fun i => m * Real.cosh (2*δ i) := by
  funext i
  unfold energy
  rw [boost_q]
  have h : m^2+(m*Real.sinh (2*δ i))^2=(m*Real.cosh (2*δ i))^2 := by
    rw [mul_pow,mul_pow,Real.cosh_sq]
    ring
  rw [h,Real.sqrt_sq (mul_nonneg hm (Real.cosh_pos _).le)]

private theorem boost_seed {m : ℝ} (hm : 0≤m) (a : ℝ) (δ : Four) :
    (fromBoost m a δ).m=m := by
  have h : mass m (fromBoost m a δ).q = (fromBoost m a δ).M := by
    rw [mass,boost_energy hm]
    rfl
  rw [State.m,← h,seed_of_mass hm]

private theorem boost_products {m : ℝ} (hm : 0≤m) (a : ℝ) (δ : Four) :
    let x := fromBoost m a δ
    upperProduct x.e x.q = m^2*coshProduct δ ∧ lowerProduct x.e x.q = m^2*sinhProduct δ := by
  let x := fromBoost m a δ
  have he : x.e=fun i => m * Real.cosh (2*δ i) := by
    change energy (fromBoost m a δ).m (fromBoost m a δ).q=_
    rw [boost_seed hm,boost_energy hm]
  have roots (i : Fin 4) :
      √(x.e i+x.q i)=√m*(Real.cosh (δ i)+Real.sinh (δ i)) ∧
      √(x.e i-x.q i)=√m*(Real.cosh (δ i)-Real.sinh (δ i)) := by
    have hp : 0≤Real.cosh (δ i)+Real.sinh (δ i) := by
      have h : Real.sinh (-(δ i))<Real.cosh (-(δ i)) := Real.sinh_lt_cosh _
      simp only [Real.sinh_neg,Real.cosh_neg] at h
      linarith
    have hn : 0≤Real.cosh (δ i)-Real.sinh (δ i) :=
      sub_nonneg.mpr (le_of_lt (Real.sinh_lt_cosh _))
    rw [he,show x.q i=m*Real.sinh (2*δ i) from boost_q m a δ i]
    simp only [Real.cosh_two_mul,Real.sinh_two_mul]
    constructor
    · rw [show m*(Real.cosh (δ i)^2+Real.sinh (δ i)^2)+m*(2*Real.sinh (δ i)*Real.cosh (δ i))=
            m*(Real.cosh (δ i)+Real.sinh (δ i))^2 by ring,
          Real.sqrt_mul hm,Real.sqrt_sq hp]
    · rw [show m*(Real.cosh (δ i)^2+Real.sinh (δ i)^2)-m*(2*Real.sinh (δ i)*Real.cosh (δ i))=
            m*(Real.cosh (δ i)-Real.sinh (δ i))^2 by ring,
          Real.sqrt_mul hm,Real.sqrt_sq hn]
  have scaled (f : Four) : prod4 (fun i => √m*f i)=m^2*prod4 f := by
    have h4 : (√m)^4=m^2 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt hm]
    calc _ = (√m)^4*prod4 f := by unfold prod4; ring
         _ = _ := by rw [h4]
  constructor
  · change prod4 (fun i => upper (x.e i) (x.q i))=_
    rw [coshProduct,← scaled (fun i => Real.cosh (δ i))]
    congr 1
    funext i
    unfold upper
    rw [(roots i).1,(roots i).2]
    ring
  · change prod4 (fun i => lower (x.e i) (x.q i))=_
    rw [sinhProduct,← scaled (fun i => Real.sinh (δ i))]
    congr 1
    funext i
    unfold lower
    rw [(roots i).1,(roots i).2]
    ring

/-- The physical-data definition of entropy is literally the plus sign of (3.77)
in the paper, for the published boost parameterization. -/
theorem boost_formula {m : ℝ} (hm : 0≤m) (a : ℝ) (δ : Four) :
    let x := fromBoost m a δ
    x.m=m ∧ x.L=m^2*(coshProduct δ+sinhProduct δ) ∧ x.R=m^2*(coshProduct δ-sinhProduct δ) ∧
    x.entropy=2*Real.pi*(m^2*(coshProduct δ+sinhProduct δ)+
      √(m^4*(coshProduct δ-sinhProduct δ)^2-x.J^2)) := by
  let x := fromBoost m a δ
  obtain ⟨hc,hs⟩ := boost_products hm a δ
  have hL : x.L=m^2*(coshProduct δ+sinhProduct δ) := by
    unfold State.L leftSector
    rw [show upperProduct x.e x.q=_ from hc,show lowerProduct x.e x.q=_ from hs]
    ring
  have hR : x.R=m^2*(coshProduct δ-sinhProduct δ) := by
    unfold State.R rightSector
    rw [show upperProduct x.e x.q=_ from hc,show lowerProduct x.e x.q=_ from hs]
    ring
  refine ⟨boost_seed hm a δ,hL,hR,?_⟩
  change 2*Real.pi*(x.L+√(x.R^2-x.J^2))=_
  rw [hL,hR,mul_pow,← pow_mul]

theorem boost_admissible {m a : ℝ} (hm : 0≤m) (ha : |a|≤m) (δ : Four) :
    (fromBoost m a δ).Admissible := by
  have hM : mass m (fromBoost m a δ).q=(fromBoost m a δ).M := by
    rw [mass,boost_energy hm]; rfl
  have hc : |sinhProduct δ|≤coshProduct δ := by
    unfold sinhProduct coshProduct
    have hid : |prod4 (fun i => Real.sinh (δ i))|=prod4 (fun i => |Real.sinh (δ i)|) := by
      simp only [prod4,abs_mul]
    rw [hid]
    apply prod_mono (fun i => abs_nonneg _)
    intro i
    have h : Real.sinh (-(δ i))<Real.cosh (-(δ i)) := Real.sinh_lt_cosh _
    simp only [Real.sinh_neg,Real.cosh_neg] at h
    exact abs_le.mpr ⟨by linarith, le_of_lt (Real.sinh_lt_cosh _)⟩
  have hd := sub_nonneg.mpr ((le_abs_self _).trans hc)
  constructor
  · rw [← hM]
    rcases hm.eq_or_lt with hz|hp
    · rw [hz]
    · exact (mass_strict le_rfl hp _).le
  · rw [(boost_formula hm a δ).2.2.1]
    change |m*a*(coshProduct δ-sinhProduct δ)|≤_
    rw [abs_mul,abs_mul,abs_of_nonneg hm,abs_of_nonneg hd,pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hm) hd

/-- The sharp theorem directly for two Kerr seeds and two arbitrary boost vectors. -/
theorem boost_superadditivity {m n a b : ℝ} (hm : 0≤m) (hn : 0≤n)
    (ha : |a|≤m) (hb : |b|≤n) (δ ε : Four) :
    let x := fromBoost m a δ
    let y := fromBoost n b ε
    (x+y).Admissible ∧ x.entropy+y.entropy+8*Real.pi*m*n≤(x+y).entropy := by
  have hx := boost_admissible hm ha δ
  have hy := boost_admissible hn hb ε
  exact ⟨(merged_sectors hx hy).1, by
    simpa only [boost_seed hm,boost_seed hn] using entropy_gap hx hy⟩

/-- The converse physical identification on the positive-seed branch. -/
theorem exists_boost_of_admissible {x : State} (hx : x.Admissible) (hm : 0<x.m) :
    ∃ (a : ℝ) (δ : Four), |a|≤x.m ∧ fromBoost x.m a δ=x := by
  let δ (i : Fin 4) := Real.arsinh (x.q i/x.m)/2
  have hq (a : ℝ) : (fromBoost x.m a δ).q=x.q := by
    funext i
    rw [boost_q,show 2*δ i=Real.arsinh (x.q i/x.m) by dsimp [δ]; ring,Real.sinh_arsinh]
    field_simp
  have hM (a : ℝ) : (fromBoost x.m a δ).M=x.M := by
    calc _ = mass x.m (fromBoost x.m a δ).q := by rw [mass,boost_energy hm.le]; rfl
         _ = x.M := by rw [hq]; exact (seed_spec hx.1).2
  have hQ (a : ℝ) : (fromBoost x.m a δ).Q=x.Q := by
    funext i
    have h := congrFun (hq a) i
    change 4*(fromBoost x.m a δ).Q i=4*x.Q i at h
    linarith
  have hr : (fromBoost x.m 0 δ).R=x.R := by
    change rightSector (energy (fromBoost x.m 0 δ).m (fromBoost x.m 0 δ).q) (fromBoost x.m 0 δ).q=_
    rw [boost_seed hm.le,hq]
    rfl
  have hfac := hr.symm.trans (boost_formula hm.le 0 δ).2.2.1
  rcases ((abs_nonneg x.J).trans hx.2).eq_or_lt with hz|hp
  · refine ⟨0,δ,by simpa using hm.le,State.ext (hM 0) ?_ (hQ 0)⟩
    have hJ := abs_le.mp hx.2
    change x.m*0*(coshProduct δ-sinhProduct δ)=x.J
    rw [mul_zero,zero_mul]
    linarith [hJ.1,hJ.2]
  · refine ⟨x.m*x.J/x.R,δ,?_,State.ext (hM _) ?_ (hQ _)⟩
    · rw [abs_div,abs_mul,abs_of_pos hm,abs_of_pos hp,div_le_iff₀ hp]
      exact mul_le_mul_of_nonneg_left hx.2 hm.le
    · change x.m*(x.m*x.J/x.R)*(coshProduct δ-sinhProduct δ)=x.J
      field_simp
      linear_combination -x.J*hfac

/-- Adding any admissible state preserves a strictly positive first seed. -/
theorem sum_seed_pos {x y : State} (hx : x.Admissible) (hy : y.Admissible) (hm : 0<x.m) :
    0<(x+y).m := by
  have hz := (mass_strict (a:=0) le_rfl hm x.q).trans_eq (seed_spec hx.1).2
  have hs : mass 0 (x+y).q < (x+y).M := by
    rw [charge_add]
    exact (zero_mass_subadd x.q y.q).trans_lt (add_lt_add_of_lt_of_le hz hy.1)
  have h := seed_spec hs.le
  change 0≤(x+y).m ∧ mass (x+y).m (x+y).q=(x+y).M at h
  rcases h.1.eq_or_lt with he|hp
  · have hh := h.2
    rw [← he] at hh
    exact False.elim ((ne_of_lt hs) hh)
  · exact hp

/-- A combined black hole is explicitly realizable in the original parameterization
whenever the first input has positive seed. -/
theorem realized_entropy_gap {x y : State} (hx : x.Admissible) (hy : y.Admissible) (hm : 0<x.m) :
    ∃ (a : ℝ) (δ : Four), |a|≤(x+y).m ∧ fromBoost (x+y).m a δ=x+y ∧
      x.entropy+y.entropy+8*Real.pi*x.m*y.m≤(fromBoost (x+y).m a δ).entropy := by
  obtain ⟨a,δ,ha,heq⟩ :=
    exists_boost_of_admissible (merged_sectors hx hy).1 (sum_seed_pos hx hy hm)
  exact ⟨a,δ,ha,heq,heq.symm ▸ entropy_gap hx hy⟩

/-- The outer-horizon area in units G = 1. -/
def State.area (x : State) := 4*x.entropy

theorem horizon_area_gap {x y : State} (hx : x.Admissible) (hy : y.Admissible) :
    x.area+y.area+32*Real.pi*x.m*y.m≤(x+y).area := by
  unfold State.area
  linarith only [entropy_gap hx hy]

def schwarzschild (M : ℝ) : State := ⟨M,0,0⟩

theorem schwarzschild_spec {M : ℝ} (hM : 0≤M) :
    (schwarzschild M).Admissible ∧ (schwarzschild M).m=M ∧
    (schwarzschild M).entropy=4*Real.pi*M^2 := by
  have heq : fromBoost M 0 0=schwarzschild M := by
    simp [fromBoost,schwarzschild,sum4,show (fun _ : Fin 4 => (0:ℝ))=(0:Four) from rfl]
    ring
  obtain ⟨hm,hL,hR,_⟩ := boost_formula hM 0 0
  rw [heq] at hm hL hR
  simp [coshProduct,sinhProduct,prod4] at hL hR
  refine ⟨heq ▸ boost_admissible hM (by simpa using hM) (0:Four),hm,?_⟩
  change 2*Real.pi*((schwarzschild M).L+√((schwarzschild M).R^2-(0:ℝ)^2))=_
  rw [hL,hR,zero_pow (by decide : 2≠0),sub_zero,Real.sqrt_sq (sq_nonneg M)]
  ring

/-- Neutral, nonrotating inputs attain equality for every pair of nonnegative masses. -/
theorem schwarzschild_equality {M N : ℝ} (hM : 0≤M) (hN : 0≤N) :
    (schwarzschild M+schwarzschild N).entropy =
      (schwarzschild M).entropy+(schwarzschild N).entropy+8*Real.pi*M*N := by
  have hs : schwarzschild M+schwarzschild N=schwarzschild (M+N) := by
    change State.mk _ (0+0) ((0:Four)+0)=State.mk _ 0 0
    simp [schwarzschild]
  rw [hs,(schwarzschild_spec (add_nonneg hM hN)).2.2,
    (schwarzschild_spec hM).2.2,(schwarzschild_spec hN).2.2]
  ring

/-- Any coefficient valid for all pairs is bounded by 8π. -/
theorem optimal_gap_coefficient {k : ℝ}
    (h : ∀ x y : State, x.Admissible → y.Admissible →
      x.entropy+y.entropy+k*x.m*y.m≤(x+y).entropy) : k ≤ 8*Real.pi := by
  obtain ⟨had,hm,_⟩ := schwarzschild_spec (show (0:ℝ)≤1 by norm_num)
  have hh := h _ _ had had
  rw [hm,schwarzschild_equality (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1)] at hh
  linarith only [hh]

end STUHorizons
