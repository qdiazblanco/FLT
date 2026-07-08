module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Torsion counting determines the group structure

If `A` is an abelian group and `#A[d] = d ^ r` for every divisor `d` of `n`, then
`A[n] ≃ (ZMod n) ^ r` (`group_theory_lemma`). The proof: produce `r` elements spanning
`A[n]` over `ℤ` (`exists_span_torsionBy`, by strong induction on `n`), then the evident
map `(ZMod n) ^ r → A[n]` is a surjection between finite groups of equal cardinality
`n ^ r`, hence an isomorphism (`nonempty_addEquiv_pi_zmod_of_span`).
-/

@[expose] public section

/-- If `a ∣ b`, the `a`-torsion of the `b`-torsion of `M` is the `a`-torsion of `M`. -/
private def torsionBySubtypeEquiv {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {a b : R} (hab : a ∣ b) :
    {x : Submodule.torsionBy R M b // a • x = 0} ≃ Submodule.torsionBy R M a where
  toFun x := ⟨x.1.1, by
    rw [Submodule.mem_torsionBy_iff]
    have h' := x.2
    rw [Subtype.ext_iff, SetLike.val_smul, ZeroMemClass.coe_zero] at h'
    exact h'⟩
  invFun y := ⟨⟨y.1, by
    obtain ⟨c, rfl⟩ := hab
    rw [Submodule.mem_torsionBy_iff, mul_comm, mul_smul,
      (Submodule.mem_torsionBy_iff _ _).mp y.2, smul_zero]⟩, by
    apply Subtype.ext
    rw [SetLike.val_smul, ZeroMemClass.coe_zero]
    exact (Submodule.mem_torsionBy_iff _ _).mp y.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl

/-- The `p`-torsion of `ZMod (p ^ c)` has exactly `p` elements, for `p` prime and `c ≥ 1`:
multiplication by `p` has image of cardinality `p ^ (c - 1)` (the multiples of `p`), hence
kernel of cardinality `p`. -/
private lemma card_zsmul_eq_zero_zmod_prime_pow {p : ℕ} (hp : p.Prime) {c : ℕ} (hc : 0 < c) :
    Nat.card {v : ZMod (p ^ c) // (p : ℤ) • v = 0} = p := by
  haveI : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  set ψp : ZMod (p ^ c) →+ ZMod (p ^ c) := zsmulAddGroupHom (p : ℤ) with hψp
  have eker : {v : ZMod (p ^ c) // (p : ℤ) • v = 0} ≃ ψp.ker :=
    Equiv.subtypeEquivRight (fun v => by
      simp only [hψp, AddMonoidHom.mem_ker, zsmulAddGroupHom_apply])
  have hrange : ψp.range = AddSubgroup.zmultiples ((p : ZMod (p ^ c))) := by
    ext y
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff, hψp,
      zsmulAddGroupHom_apply]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, mul_comm]
    · rintro ⟨w, rfl⟩
      refine ⟨((w : ℤ) : ZMod (p ^ c)), ?_⟩
      rw [zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
  have hsplit : p ^ c = p ^ (c - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hc]
  have lag : Nat.card (ZMod (p ^ c)) =
      Nat.card (ZMod (p ^ c) ⧸ ψp.ker) * Nat.card ψp.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have hq : Nat.card (ZMod (p ^ c) ⧸ ψp.ker) = p ^ (c - 1) := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψp).toEquiv, hrange,
      Nat.card_zmultiples, ZMod.addOrderOf_coe _ (NeZero.ne _),
      Nat.gcd_eq_right (dvd_pow_self p hc.ne'), hsplit, Nat.mul_div_cancel _ hp.pos]
  have hker : Nat.card ψp.ker = p := by
    have h6 := lag
    rw [Nat.card_zmod, hq] at h6
    refine (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (c - 1)) ?_).symm
    rw [← h6, hsplit]
  rw [Nat.card_congr eker, hker]

/-- An integer multiple of an element of a direct sum vanishes iff it vanishes
componentwise. -/
private lemma zsmul_eq_zero_iff_forall {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (c : ℤ) (y : DirectSum ι M) : c • y = 0 ↔ ∀ i, c • y i = 0 := by
  have hsa : ∀ (z : DirectSum ι M) (j : ι), (c • z) j = c • z j :=
    fun z j => DirectSum.smul_apply c z j
  constructor
  · intro hy i
    have h6 : (c • y) i = (0 : DirectSum ι M) i := by rw [hy]
    rw [hsa, DirectSum.zero_apply] at h6
    exact h6
  · intro hy
    ext i
    rw [hsa, DirectSum.zero_apply]
    exact hy i

/-- A submodule additively isomorphic to a finite direct sum `⨁ i, ZMod (ms i)` is spanned
over `ℤ` by the images of the standard generators. -/
private lemma le_span_range_symm_of {A : Type*} [AddCommGroup A] {T : Submodule ℤ A}
    {ι : Type} [Finite ι] [DecidableEq ι] {ms : ι → ℕ} (hms : ∀ i, ms i ≠ 0)
    (φ : T ≃+ DirectSum ι fun i => ZMod (ms i)) :
    T ≤ Submodule.span ℤ
      (Set.range fun i => (φ.symm (DirectSum.of (fun i => ZMod (ms i)) i 1) : A)) := by
  haveI := Fintype.ofFinite ι
  intro x hx
  have hsingle : ∀ (i : ι) (v : ZMod (ms i)),
      ((v.val : ℤ) • DirectSum.of (fun i => ZMod (ms i)) i (1 : ZMod (ms i))) =
        DirectSum.of (fun i => ZMod (ms i)) i v := by
    intro i v
    haveI : NeZero (ms i) := ⟨hms i⟩
    rw [← map_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  set t : T := ⟨x, hx⟩
  have expand : t = ∑ i, (((φ t) i).val : ℤ) •
      φ.symm (DirectSum.of (fun i => ZMod (ms i)) i 1) := by
    apply φ.injective
    rw [map_sum]
    simp_rw [map_zsmul, AddEquiv.apply_symm_apply, hsingle]
    exact (DirectSum.sum_univ_of (φ t)).symm
  have hx_eq : x = ∑ i, (((φ t) i).val : ℤ) •
      (φ.symm (DirectSum.of (fun i => ZMod (ms i)) i 1) : A) := by
    have h9 := congrArg Subtype.val expand
    simpa using h9
  rw [hx_eq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- **Prime-power case of the torsion-counting criterion.** If `A[p]` has `p ^ r` elements
and `A[p ^ k]` has `(p ^ k) ^ r` elements, then `A[p ^ k]` is spanned over `ℤ` by `r`
elements: the classification of finite abelian groups writes `A[p ^ k]` as a finite direct
sum of nontrivial cyclic `p`-groups, and counting the `p`-torsion of both sides shows there
are exactly `r` summands. -/
private lemma exists_span_torsionBy_prime_pow {A : Type*} [AddCommGroup A] (r : ℕ) {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k)
    (hcard : Nat.card (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) = (p ^ k) ^ r)
    (hcardp : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ r) :
    ∃ z : Fin r → A, (∀ j, ((p ^ k : ℕ) : ℤ) • z j = 0) ∧
      ∀ x : A, ((p ^ k : ℕ) : ℤ) • x = 0 → x ∈ Submodule.span ℤ (Set.range z) := by
  classical
  haveI : Finite (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (pow_ne_zero _ hp.pos.ne'))
  obtain ⟨ι, hι, ms, hms1, ⟨φ⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite' (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ))
  haveI := hι
  -- each summand is killed by `p ^ k`, so is a nontrivial cyclic `p`-group
  have hms_dvd : ∀ i, ms i ∣ p ^ k := by
    intro i
    have h2 : ((p ^ k : ℕ) : ℤ) •
        DirectSum.of (fun i => ZMod (ms i)) i (1 : ZMod (ms i)) = 0 := by
      rw [← φ.apply_symm_apply (DirectSum.of (fun i => ZMod (ms i)) i 1), ← map_zsmul,
        Submodule.smul_torsionBy, map_zero]
    rw [natCast_zsmul] at h2
    have h4 := addOrderOf_dvd_of_nsmul_eq_zero h2
    rwa [addOrderOf_injective (DirectSum.of (fun i => ZMod (ms i)) i)
      (DirectSum.of_injective i), ZMod.addOrderOf_one] at h4
  -- counting the `p`-torsion two ways pins down the number of summands
  have hcount1 : Nat.card
      {t : Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ) // (p : ℤ) • t = 0} = p ^ r :=
    (Nat.card_congr
      (torsionBySubtypeEquiv (Int.natCast_dvd_natCast.mpr (dvd_pow_self p hk.ne')))).trans
      hcardp
  have hcount2 : Nat.card
      {t : Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ) // (p : ℤ) • t = 0} =
      p ^ Fintype.card ι := by
    have perfactor : ∀ i, Nat.card {v : ZMod (ms i) // (p : ℤ) • v = 0} = p := by
      intro i
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp (hms_dvd i)
      have hc0 : 0 < c :=
        Nat.pos_of_ne_zero (by rintro rfl; have h5 := hms1 i; rw [hc] at h5; simp at h5)
      rw [hc]
      exact card_zsmul_eq_zero_zmod_prime_pow hp hc0
    have e2 : {t : Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ) // (p : ℤ) • t = 0} ≃
        ∀ i, {v : ZMod (ms i) // (p : ℤ) • v = 0} :=
      (φ.toEquiv.subtypeEquiv fun t =>
        (⟨fun ht => by rw [← map_zsmul φ, ht, map_zero],
          fun ht => by
            have h7 := congrArg φ.symm ht
            rw [map_zsmul, AddEquiv.symm_apply_apply, map_zero] at h7
            exact h7⟩ :
          (p : ℤ) • t = 0 ↔ (p : ℤ) • φ t = 0)).trans <|
      (Equiv.subtypeEquivRight fun y => zsmul_eq_zero_iff_forall (p : ℤ) y).trans <|
      (((DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (ms i))).toEquiv).subtypeEquiv
        fun y => Iff.rfl).trans
      (Equiv.subtypePiEquivPi (p := fun i (v : ZMod (ms i)) => (p : ℤ) • v = 0))
    rw [Nat.card_congr e2, Nat.card_pi]
    exact (Finset.prod_congr rfl fun i _ => perfactor i).trans
      (by rw [Finset.prod_const, Finset.card_univ])
  have hcard_ι : Fintype.card ι = r :=
    Nat.pow_right_injective hp.two_le (hcount2.symm.trans hcount1)
  let σ : Fin r ≃ ι := (Fintype.equivFinOfCardEq hcard_ι).symm
  refine ⟨fun j => (φ.symm (DirectSum.of (fun i => ZMod (ms i)) (σ j) 1) : A),
    fun j => ?_, fun x hx => ?_⟩
  · have h8 := Submodule.smul_torsionBy (M := A) _
      (φ.symm (DirectSum.of (fun i => ZMod (ms i)) (σ j) 1))
    rw [Subtype.ext_iff, SetLike.val_smul, ZeroMemClass.coe_zero] at h8
    exact h8
  · have hrange : (Set.range fun j =>
        (φ.symm (DirectSum.of (fun i => ZMod (ms i)) (σ j) 1) : A)) =
        Set.range fun i => (φ.symm (DirectSum.of (fun i => ZMod (ms i)) i 1) : A) :=
      σ.surjective.range_comp
        (fun i => (φ.symm (DirectSum.of (fun i => ZMod (ms i)) i 1) : A))
    rw [hrange]
    exact le_span_range_symm_of (fun i => (Nat.zero_lt_of_lt (hms1 i)).ne') φ
      ((Submodule.mem_torsionBy_iff _ _).mpr hx)

/-- **Bezout trick.** If `a` and `b` are coprime, `b` kills every `s' j`, and the
`a`-torsion lies in the `ℤ`-span of the `s j`, then the `a`-torsion lies in the `ℤ`-span of
the `s j + s' j`: indeed `w = b • (v • w)` where `u * a + v * b = 1`, and
`b • (s j + s' j) = b • s j`. -/
private lemma mem_span_range_add_of_isCoprime {A : Type*} [AddCommGroup A] {ι : Type*}
    [Finite ι] {a b : ℤ} (hab : IsCoprime a b) {s s' : ι → A} (hs' : ∀ j, b • s' j = 0)
    (hspan : ∀ w, a • w = 0 → w ∈ Submodule.span ℤ (Set.range s)) :
    ∀ w, a • w = 0 → w ∈ Submodule.span ℤ (Set.range fun j => s j + s' j) := by
  haveI := Fintype.ofFinite ι
  obtain ⟨u, v, huv⟩ := hab
  intro w hw
  have e : w = b • (v • w) := by
    calc w = (1 : ℤ) • w := (one_smul _ _).symm
    _ = (u * a + v * b) • w := by rw [huv]
    _ = u • (a • w) + (v * b) • w := by rw [add_smul, mul_smul]
    _ = (v * b) • w := by rw [hw, smul_zero, zero_add]
    _ = b • (v • w) := by rw [mul_comm, mul_smul]
  have hv : a • (v • w) = 0 := by rw [smul_comm, hw, smul_zero]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan _ hv)
  rw [e, ← hc, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h11 : b • c j • s j = c j • (b • (s j + s' j)) := by
    rw [smul_add, hs' j, add_zero, smul_comm]
  rw [h11]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j)))

/-- If `A[d]` has `d ^ r` elements for every divisor `d` of `m`, then `A[m]` is spanned
over `ℤ` by `r` elements. Strong induction on `m`: split off the largest power of the least
prime factor and combine generators of the two coprime torsion parts. -/
private lemma exists_span_torsionBy {A : Type*} [AddCommGroup A] (r : ℕ) :
    ∀ m : ℕ, 0 < m →
      (∀ d : ℕ, d ∣ m → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) →
      ∃ z : Fin r → A, (∀ j, (m : ℤ) • z j = 0) ∧
        ∀ x : A, (m : ℤ) • x = 0 → x ∈ Submodule.span ℤ (Set.range z) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro hm hh
  have hm1 : 1 ≤ m := hm
  rcases eq_or_lt_of_le hm1 with h1 | h1
  · -- `m = 1`: only `0` is killed by `1`
    refine ⟨fun _ => 0, fun _ => smul_zero _, fun x hx => ?_⟩
    rw [← h1] at hx
    have hx0 : x = 0 := by simpa using hx
    simp [hx0]
  · -- `1 < m`: write `m = p ^ k * b` with `p` the least prime factor, `p ∤ b`
    have hm0 : m ≠ 0 := by omega
    have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
    set p := m.minFac
    set k := m.factorization p
    have hk : 0 < k := hp.factorization_pos_of_dvd hm0 (Nat.minFac_dvd m)
    have hadvd : p ^ k ∣ m := Nat.ordProj_dvd m p
    obtain ⟨b, hab⟩ : ∃ b, p ^ k * b = m := ⟨m / p ^ k, Nat.mul_div_cancel' hadvd⟩
    have ha1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hab; omega)
    by_cases hb1 : b = 1
    · -- prime-power case
      have hm_eq : m = p ^ k := by rw [← hab, hb1, mul_one]
      rw [hm_eq]
      exact exists_span_torsionBy_prime_pow r hp hk (hm_eq ▸ hh m dvd_rfl)
        (hh p (Nat.minFac_dvd m))
    · -- coprime-splitting case
      have hb1' : 1 < b := by omega
      have ha_lt : p ^ k < m := by
        calc p ^ k = p ^ k * 1 := (mul_one _).symm
        _ < p ^ k * b := mul_lt_mul_of_pos_left hb1' (by positivity)
        _ = m := hab
      have hb_lt : b < m := by
        calc b = 1 * b := (one_mul _).symm
        _ < p ^ k * b := mul_lt_mul_of_pos_right ha1 hb0
        _ = m := hab
      have hpb : ¬ p ∣ b := by
        intro hpb
        have h10 : p ^ (k + 1) ∣ m := by
          rw [← hab, pow_succ]
          exact mul_dvd_mul dvd_rfl hpb
        rw [hp.pow_dvd_iff_le_factorization hm0] at h10
        omega
      have hcop : Nat.Coprime (p ^ k) b :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)
      obtain ⟨xs, hxkill, hxspan⟩ := IH (p ^ k) ha_lt (by positivity)
        (fun d hd => hh d (hd.trans hadvd))
      obtain ⟨ys, hykill, hyspan⟩ := IH b hb_lt hb0
        (fun d hd => hh d (hd.trans ⟨p ^ k, by rw [mul_comm]; exact hab.symm⟩))
      have hmZ : (m : ℤ) = ((p ^ k : ℕ) : ℤ) * (b : ℤ) := by exact_mod_cast hab.symm
      have hcopZ : IsCoprime ((p ^ k : ℕ) : ℤ) ((b : ℕ) : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast hcop
      refine ⟨fun j => xs j + ys j, fun j => ?_, fun w hw => ?_⟩
      · rw [hmZ, smul_add]
        have h12 : (((p ^ k : ℕ) : ℤ) * (b : ℤ)) • xs j = 0 := by
          rw [mul_comm, mul_smul, hxkill j, smul_zero]
        have h13 : (((p ^ k : ℕ) : ℤ) * (b : ℤ)) • ys j = 0 := by
          rw [mul_smul, hykill j, smul_zero]
        rw [h12, h13, add_zero]
      · obtain ⟨u, v, huv⟩ := id hcopZ
        have decompose : w = (u * ((p ^ k : ℕ) : ℤ)) • w + (v * (b : ℤ)) • w := by
          rw [← add_smul, huv, one_smul]
        have hw_a : ((p ^ k : ℕ) : ℤ) • ((v * (b : ℤ)) • w) = 0 := by
          rw [smul_smul,
            show ((p ^ k : ℕ) : ℤ) * (v * (b : ℤ)) = v * (((p ^ k : ℕ) : ℤ) * (b : ℤ))
              by ring,
            ← hmZ, mul_smul, hw, smul_zero]
        have hw_b : (b : ℤ) • ((u * ((p ^ k : ℕ) : ℤ)) • w) = 0 := by
          rw [smul_smul,
            show (b : ℤ) * (u * ((p ^ k : ℕ) : ℤ)) = u * (((p ^ k : ℕ) : ℤ) * (b : ℤ))
              by ring,
            ← hmZ, mul_smul, hw, smul_zero]
        rw [decompose]
        refine Submodule.add_mem _ ?_ ?_
        · have h14 := mem_span_range_add_of_isCoprime hcopZ.symm hxkill hyspan _ hw_b
          have hfe : (fun j => ys j + xs j) = fun j => xs j + ys j := by
            funext j
            rw [add_comm]
          rwa [hfe] at h14
        · exact mem_span_range_add_of_isCoprime hcopZ hykill hxspan _ hw_a

/-- **Spanning elements plus counting give the isomorphism.** If the `n`-torsion of `A` has
`n ^ r` elements and is spanned over `ℤ` by `r` elements, then it is isomorphic to
`(ZMod n) ^ r`: the map sending the standard basis to the spanning elements is a surjection
between finite groups of the same cardinality. -/
private lemma nonempty_addEquiv_pi_zmod_of_span {A : Type*} [AddCommGroup A] {n : ℕ}
    (hn : 0 < n) {r : ℕ} (hcard : Nat.card (Submodule.torsionBy ℤ A n) = n ^ r)
    {z : Fin r → A} (hz : ∀ j, (n : ℤ) • z j = 0)
    (hspan : ∀ x : A, (n : ℤ) • x = 0 → x ∈ Submodule.span ℤ (Set.range z)) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → ZMod n)) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite (Submodule.torsionBy ℤ A (n : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hzT : ∀ j, z j ∈ Submodule.torsionBy ℤ A (n : ℤ) := fun j =>
    (Submodule.mem_torsionBy_iff _ _).mpr (hz j)
  let f : Fin r → (ZMod n →+ Submodule.torsionBy ℤ A (n : ℤ)) := fun j =>
    ZMod.lift n ⟨zmultiplesHom _ ⟨z j, hzT j⟩, Subtype.ext (by simpa using hz j)⟩
  let ψ : (Fin r → ZMod n) →+ Submodule.torsionBy ℤ A (n : ℤ) :=
    ∑ j, (f j).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) j)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (hspan x ((Submodule.mem_torsionBy_iff _ _).mp hx))
    refine ⟨fun j => ((c j : ℤ) : ZMod n), Subtype.ext ?_⟩
    have hval : (ψ (fun j => ((c j : ℤ) : ZMod n)) : A) = ∑ j, c j • z j := by
      simp only [ψ, f, AddMonoidHom.finsetSum_apply, AddMonoidHom.coe_comp,
        Function.comp_apply, Pi.evalAddMonoidHom_apply, ZMod.lift_coe, zmultiplesHom_apply,
        AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rw [hval]
    exact hc
  have hcards : Nat.card (Fin r → ZMod n) =
      Nat.card (Submodule.torsionBy ℤ A (n : ℤ)) := by
    rw [Nat.card_pi, hcard]
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ⟨(AddEquiv.ofBijective ψ
    ((Nat.bijective_iff_surjective_and_card ψ).mpr ⟨hsurj, hcards⟩)).symm⟩

-- This theorem was well-known in the early part of the 20th century.
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  obtain ⟨z, hz, hspan⟩ := exists_span_torsionBy r n hn h
  exact nonempty_addEquiv_pi_zmod_of_span hn (h n dvd_rfl) hz hspan
