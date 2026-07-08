module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep


@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  classical
  -- The heart of the proof: the `m`-torsion of `A` is spanned over `ℤ` by `r` elements,
  -- shown by strong induction on `m`. Granted this, the map `(ZMod m)^r → A[m]` sending
  -- the standard basis to these generators is a surjection between finite groups of the
  -- same cardinality `m ^ r`, hence an isomorphism.
  have key : ∀ m : ℕ, 0 < m →
      (∀ d : ℕ, d ∣ m → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) →
      ∃ z : Fin r → A, (∀ j, (m : ℤ) • z j = 0) ∧
        ∀ x : A, (m : ℤ) • x = 0 → x ∈ Submodule.span ℤ (Set.range z) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
    intro hm hh
    have hm1 : 1 ≤ m := hm
    rcases eq_or_lt_of_le hm1 with h1 | h1
    · -- `m = 1`: only `0` is killed by `1`.
      refine ⟨fun _ => 0, fun _ => smul_zero _, fun x hx => ?_⟩
      rw [← h1] at hx
      have hx0 : x = 0 := by simpa using hx
      simp [hx0]
    · -- `1 < m`: write `m = p ^ k * b` with `p` the least prime factor of `m`,
      -- `k = v_p(m) ≥ 1` and `p ∤ b`, so that `p ^ k` and `b` are coprime.
      have hm0 : m ≠ 0 := by omega
      have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
      set p := m.minFac with hp_def
      set k := m.factorization p with hk_def
      have hk : 0 < k := hp.factorization_pos_of_dvd hm0 (Nat.minFac_dvd m)
      have hadvd : p ^ k ∣ m := Nat.ordProj_dvd m p
      obtain ⟨b, hab⟩ : ∃ b, p ^ k * b = m := ⟨m / p ^ k, Nat.mul_div_cancel' hadvd⟩
      have ha1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with rfl | hb0
        · rw [mul_zero] at hab; omega
        · exact hb0
      by_cases hb1 : b = 1
      · -- ** The prime-power case `m = p ^ k`. **
        -- Decompose `A[m]` by the classification of finite abelian groups; counting the
        -- `p`-torsion shows there are exactly `r` cyclic summands, and their generators
        -- span. (Their orders are pinned down automatically by `#A[m] = m ^ r`.)
        have hm_eq : m = p ^ k := by rw [← hab, hb1, mul_one]
        have hTcard : Nat.card (Submodule.torsionBy ℤ A (m : ℤ)) = m ^ r := hh m dvd_rfl
        haveI : Finite (Submodule.torsionBy ℤ A (m : ℤ)) :=
          Nat.finite_of_card_ne_zero (by rw [hTcard]; positivity)
        obtain ⟨ι, hι, ms, hms1, ⟨φ⟩⟩ :=
          AddCommGroup.equiv_directSum_zmod_of_finite' (Submodule.torsionBy ℤ A (m : ℤ))
        haveI := hι
        have hkill : ∀ t : Submodule.torsionBy ℤ A (m : ℤ), (m : ℤ) • t = 0 := fun t =>
          Subtype.ext (by
            rw [SetLike.val_smul, ZeroMemClass.coe_zero]
            exact (Submodule.mem_torsionBy_iff _ _).mp t.2)
        -- each cyclic summand is killed by `m`, so its order divides `m = p ^ k`
        have hms_dvd : ∀ i, ms i ∣ m := by
          intro i
          have h2 : (m : ℤ) • DirectSum.of (fun i => ZMod (ms i)) i (1 : ZMod (ms i)) = 0 := by
            rw [← φ.apply_symm_apply (DirectSum.of (fun i => ZMod (ms i)) i 1), ← map_zsmul,
              hkill, map_zero]
          rw [natCast_zsmul] at h2
          have h4 := addOrderOf_dvd_of_nsmul_eq_zero h2
          rwa [addOrderOf_injective (DirectSum.of (fun i => ZMod (ms i)) i)
            (DirectSum.of_injective i), ZMod.addOrderOf_one] at h4
        have hms_pow : ∀ i, ∃ c, 0 < c ∧ ms i = p ^ c := by
          intro i
          obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).mp (hm_eq ▸ hms_dvd i)
          refine ⟨c, ?_, hc⟩
          rcases Nat.eq_zero_or_pos c with rfl | h0
          · have h5 := hms1 i
            rw [hc] at h5
            simp at h5
          · exact h0
        -- The `p`-torsion of `A[m]` is `A[p]`, of cardinality `p ^ r` by hypothesis...
        have e1 : {t : Submodule.torsionBy ℤ A (m : ℤ) // (p : ℤ) • t = 0} ≃
            Submodule.torsionBy ℤ A (p : ℤ) :=
          { toFun := fun t => ⟨t.1.1, by
              rw [Submodule.mem_torsionBy_iff]
              have h' := t.2
              rw [Subtype.ext_iff, SetLike.val_smul, ZeroMemClass.coe_zero] at h'
              exact h'⟩
            invFun := fun s => ⟨⟨s.1, by
              rw [Submodule.mem_torsionBy_iff]
              have hs := (Submodule.mem_torsionBy_iff _ _).mp s.2
              have hsplit : (m : ℤ) = (p : ℤ) ^ (k - 1) * (p : ℤ) := by
                rw [hm_eq]
                push_cast
                rw [← pow_succ, Nat.sub_add_cancel hk]
              rw [hsplit, mul_smul, hs, smul_zero]⟩, by
              apply Subtype.ext
              rw [SetLike.val_smul, ZeroMemClass.coe_zero]
              exact (Submodule.mem_torsionBy_iff _ _).mp s.2⟩
            left_inv := fun t => Subtype.ext (Subtype.ext rfl)
            right_inv := fun s => Subtype.ext rfl }
        have hcount1 : Nat.card {t : Submodule.torsionBy ℤ A (m : ℤ) // (p : ℤ) • t = 0} =
            p ^ r := (Nat.card_congr e1).trans (hh p (Nat.minFac_dvd m))
        -- ... and componentwise it has cardinality `p ^ #ι`, because the `p`-torsion of
        -- `ZMod (p ^ c)` has exactly `p` elements (kernel/image counting for `p • ·`).
        have perfactor : ∀ i, Nat.card {v : ZMod (ms i) // (p : ℤ) • v = 0} = p := by
          intro i
          obtain ⟨c, hc0, hc⟩ := hms_pow i
          rw [hc]
          haveI : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.pos.ne'⟩
          set ψp : ZMod (p ^ c) →+ ZMod (p ^ c) := zsmulAddGroupHom (p : ℤ) with hψp
          have eker : {v : ZMod (p ^ c) // (p : ℤ) • v = 0} ≃ ψp.ker :=
            Equiv.subtypeEquivRight (fun v => by
              simp [hψp, AddMonoidHom.mem_ker])
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
            rw [← pow_succ, Nat.sub_add_cancel hc0]
          have lag : Nat.card (ZMod (p ^ c)) =
              Nat.card (ZMod (p ^ c) ⧸ ψp.ker) * Nat.card ψp.ker :=
            AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
          have hq : Nat.card (ZMod (p ^ c) ⧸ ψp.ker) = p ^ (c - 1) := by
            rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψp).toEquiv, hrange,
              Nat.card_zmultiples, ZMod.addOrderOf_coe _ (NeZero.ne _),
              Nat.gcd_eq_right (dvd_pow_self p hc0.ne'), hsplit,
              Nat.mul_div_cancel _ hp.pos]
          have hker : Nat.card ψp.ker = p := by
            have h6 := lag
            rw [Nat.card_zmod, hq] at h6
            refine (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (c - 1)) ?_).symm
            rw [← h6, hsplit]
          rw [Nat.card_congr eker, hker]
        -- comparing the two counts pins down the number of summands
        have hsa : ∀ (y : DirectSum ι fun i => ZMod (ms i)) (j : ι),
            ((p : ℤ) • y) j = (p : ℤ) • (y j) :=
          fun y j => DirectSum.smul_apply (p : ℤ) y j
        have hcomp : ∀ y : DirectSum ι fun i => ZMod (ms i),
            ((p : ℤ) • y = 0 ↔ ∀ i, (p : ℤ) • (y i) = 0) := by
          intro y
          constructor
          · intro hy i
            have h6 : ((p : ℤ) • y) i = (0 : DirectSum ι fun i => ZMod (ms i)) i := by rw [hy]
            rw [hsa, DirectSum.zero_apply] at h6
            exact h6
          · intro hy
            ext i
            rw [hsa, DirectSum.zero_apply]
            exact hy i
        have hcount2 : Nat.card {t : Submodule.torsionBy ℤ A (m : ℤ) // (p : ℤ) • t = 0} =
            p ^ Fintype.card ι := by
          have e2 : {t : Submodule.torsionBy ℤ A (m : ℤ) // (p : ℤ) • t = 0} ≃
              ∀ i, {v : ZMod (ms i) // (p : ℤ) • v = 0} :=
            (φ.toEquiv.subtypeEquiv fun t =>
              (⟨fun ht => by rw [← map_zsmul φ, ht, map_zero],
                fun ht => by
                  have h7 := congrArg φ.symm ht
                  rw [map_zsmul, AddEquiv.symm_apply_apply, map_zero] at h7
                  exact h7⟩ :
                (p : ℤ) • t = 0 ↔ (p : ℤ) • φ t = 0)).trans <|
            (Equiv.subtypeEquivRight hcomp).trans <|
            (((DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (ms i))).toEquiv).subtypeEquiv
              fun y => Iff.rfl).trans
            (Equiv.subtypePiEquivPi (p := fun i (v : ZMod (ms i)) => (p : ℤ) • v = 0))
          rw [Nat.card_congr e2, Nat.card_pi]
          exact (Finset.prod_congr rfl fun i _ => perfactor i).trans
            (by rw [Finset.prod_const, Finset.card_univ])
        have hcard_ι : Fintype.card ι = r :=
          Nat.pow_right_injective hp.two_le (hcount2.symm.trans hcount1)
        -- the images of the standard generators of the direct sum span `A[m]`
        let σ : Fin r ≃ ι := (Fintype.equivFinOfCardEq hcard_ι).symm
        refine ⟨fun j => (φ.symm (DirectSum.of (fun i => ZMod (ms i)) (σ j) 1) : A),
          fun j => ?_, fun x hx => ?_⟩
        · have h8 := hkill (φ.symm (DirectSum.of (fun i => ZMod (ms i)) (σ j) 1))
          rw [Subtype.ext_iff, SetLike.val_smul, ZeroMemClass.coe_zero] at h8
          exact h8
        · have hsingle : ∀ (i : ι) (v : ZMod (ms i)),
              ((v.val : ℤ) • DirectSum.of (fun i => ZMod (ms i)) i (1 : ZMod (ms i))) =
                DirectSum.of (fun i => ZMod (ms i)) i v := by
            intro i v
            haveI : NeZero (ms i) := ⟨by have := hms1 i; omega⟩
            rw [← map_zsmul]
            congr 1
            rw [zsmul_eq_mul, mul_one]
            push_cast
            rw [ZMod.natCast_val, ZMod.cast_id]
          set t : Submodule.torsionBy ℤ A (m : ℤ) :=
            ⟨x, (Submodule.mem_torsionBy_iff _ _).mpr hx⟩ with ht_def
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
          apply Submodule.sum_mem
          intro i _
          refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ.symm i, ?_⟩)
          exact congrArg
            (fun i' => (φ.symm (DirectSum.of (fun i => ZMod (ms i)) i' (1 : ZMod (ms i'))) : A))
            (σ.apply_symm_apply i)
      · -- ** The coprime factorisation case `m = p ^ k * b` with `1 < p ^ k, b < m`. **
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
        -- Generic half: if `u' * a' + v' * b' = 1`, anything killed by `a'` lies in the
        -- span of the `s j + s' j`, provided the `s j` span the `a'`-torsion and the
        -- `s' j` are killed by `b'`. (Key point: `w' = b' • (v' • w')` by Bezout, and
        -- `b' • (s j + s' j) = b' • s j`.)
        have half : ∀ (a' b' u' v' : ℤ) (s s' : Fin r → A),
            u' * a' + v' * b' = 1 →
            (∀ j, b' • s' j = 0) →
            (∀ w', a' • w' = 0 → w' ∈ Submodule.span ℤ (Set.range s)) →
            ∀ w', a' • w' = 0 →
              w' ∈ Submodule.span ℤ (Set.range fun j => s j + s' j) := by
          intro a' b' u' v' s s' huv' hs' hspan' w' hw'
          have e : w' = b' • (v' • w') := by
            calc w' = (1 : ℤ) • w' := (one_smul _ _).symm
            _ = (u' * a' + v' * b') • w' := by rw [huv']
            _ = u' • (a' • w') + (v' * b') • w' := by rw [add_smul, mul_smul]
            _ = (v' * b') • w' := by rw [hw', smul_zero, zero_add]
            _ = b' • (v' • w') := by rw [mul_comm, mul_smul]
          have hv : a' • (v' • w') = 0 := by rw [smul_comm, hw', smul_zero]
          obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan' _ hv)
          rw [e, ← hc, Finset.smul_sum]
          apply Submodule.sum_mem
          intro j _
          have h11 : b' • c j • s j = c j • (b' • (s j + s' j)) := by
            rw [smul_add, hs' j, add_zero, smul_comm]
          rw [h11]
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_range_self j)))
        refine ⟨fun j => xs j + ys j, fun j => ?_, fun w hw => ?_⟩
        · rw [hmZ, smul_add]
          have h12 : (((p ^ k : ℕ) : ℤ) * (b : ℤ)) • xs j = 0 := by
            rw [mul_comm, mul_smul, hxkill j, smul_zero]
          have h13 : (((p ^ k : ℕ) : ℤ) * (b : ℤ)) • ys j = 0 := by
            rw [mul_smul, hykill j, smul_zero]
          rw [h12, h13, add_zero]
        · have hcopZ : IsCoprime ((p ^ k : ℕ) : ℤ) ((b : ℕ) : ℤ) := by
            rw [Int.isCoprime_iff_gcd_eq_one]
            exact_mod_cast hcop
          obtain ⟨u, v, huv⟩ := hcopZ
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
          · have h14 := half (b : ℤ) ((p ^ k : ℕ) : ℤ) v u ys xs
              (by linarith [huv]) hxkill hyspan _ hw_b
            have hfe : (fun j => ys j + xs j) = fun j => xs j + ys j := by
              funext j
              rw [add_comm]
            rwa [hfe] at h14
          · exact half ((p ^ k : ℕ) : ℤ) (b : ℤ) u v xs ys huv hykill hxspan _ hw_a
  -- The endgame: turn the `r` spanning elements into an isomorphism by counting.
  obtain ⟨z, hz, hspan⟩ := key n hn h
  haveI : NeZero n := ⟨hn.ne'⟩
  have hTcard : Nat.card (Submodule.torsionBy ℤ A (n : ℤ)) = n ^ r := h n dvd_rfl
  haveI : Finite (Submodule.torsionBy ℤ A (n : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; positivity)
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
      simp [ψ, f, ZMod.lift_coe, zmultiplesHom_apply]
    rw [hval]
    exact hc
  have hcards : Nat.card (Fin r → ZMod n) =
      Nat.card (Submodule.torsionBy ℤ A (n : ℤ)) := by
    rw [Nat.card_pi, hTcard]
    simp
  exact ⟨(AddEquiv.ofBijective ψ
    ((Nat.bijective_iff_surjective_and_card ψ).mpr ⟨hsurj, hcards⟩)).symm⟩
