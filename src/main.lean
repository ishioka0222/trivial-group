import data.nat.basic

def triv : set nat := { 1 }

lemma mem_one (a : nat) : a ∈ triv ↔ a = 1 := iff.rfl

lemma mul (a b : nat) : a ∈ triv → b ∈ triv → nat.mul a b = 1 :=
  assume ha_in_triv : a ∈ triv,
  assume hb_in_triv : b ∈ triv,
  have ha_one : a = 1, from iff.mp (mem_one a) ha_in_triv,
  have hb_one : b = 1, from iff.mp (mem_one b) hb_in_triv,
  show nat.mul a b = 1, from
    calc
      nat.mul a b = nat.mul 1 b : by rw ha_one
              ... = nat.mul 1 1 : by rw hb_one
              ... = 1 : one_mul 1

def triv_mul (a b : triv) : triv := ⟨ nat.mul a b, mul a b a.property b.property ⟩
instance : has_mul triv := ⟨ triv_mul ⟩

def triv_one : triv := ⟨1, rfl⟩
instance : has_one triv := ⟨ triv_one ⟩

def one (a : triv) : a = 1 :=
  have h : ↑a = 1, from
    calc
      ↑a = 1 : iff.mp (mem_one a) a.property,
  subtype.ext h

def triv_mul_one (a : triv) : a * 1 = a :=
  have h : ↑(a * 1) = ↑a, from
    calc
      ↑(a * 1) = ↑(triv_mul a 1) : rfl
            ... = nat.mul ↑a 1 : rfl
            ... = (↑a) * 1 : rfl
            ... = ↑a : by rw nat.mul_one,
  subtype.ext h

def triv_one_mul (a : triv) : 1 * a = a :=
  have h : ↑(1 * a) = ↑a, from
    calc
      ↑(1 * a) = ↑(triv_mul 1 a) : rfl
            ... = nat.mul 1 ↑a : rfl
            ... = 1 * (↑a): rfl
            ... = ↑a : by rw nat.one_mul,
  subtype.ext h

def triv_mul_assoc (a b c : triv) : (a * b) * c = a * (b * c) :=
  have h : ↑((a * b) * c) = ↑(a * (b * c)), from
    calc
      ↑((a * b) * c) = ↑(triv_mul (triv_mul a b) c) : rfl
                  ... = nat.mul (nat.mul ↑a ↑b) ↑c : rfl
                  ... = (↑a * ↑b) * ↑c : rfl
                  ... = ↑a * (↑b * ↑c) : by rw nat.mul_assoc
                  ... = nat.mul ↑a (nat.mul ↑b ↑c) : rfl
                  ... = ↑(a * (b * c)) : rfl,
  subtype.ext h

def triv_inv (a : triv) : triv := a
instance : has_inv triv := ⟨ triv_inv ⟩

def triv_mul_left_inv (a : triv) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a * a : rfl
        ... = a * 1 : by rw one a
        ... = a : by rw triv_mul_one a
        ... = 1 : by rw one a

instance : group triv :=
{
  mul := triv_mul,
  one := triv_one,
  mul_one := triv_mul_one,
  one_mul := triv_one_mul,
  mul_assoc := triv_mul_assoc,
  inv := triv_inv,
  mul_left_inv := triv_mul_left_inv
}
