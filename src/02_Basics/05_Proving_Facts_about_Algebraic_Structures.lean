import topology.metric_space.basic

section
variables {α : Type*} [partial_order α]
variables x y z : α

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
lt_iff_le_and_ne

end

section
variables {α : Type*} [lattice α]
variables x y z : α

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

-- le_refl, le_trans,

#check le_refl
#check le_trans
#check le_antisymm -- le_antisymm : ?M_3 ≤ ?M_4 → ?M_4 ≤ ?M_3 → ?M_3 = ?M_4

example : x ⊓ y = y ⊓ x := begin
  apply le_antisymm,
  { show x ⊓ y ≤ y ⊓ x,
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,
  },
  { show y ⊓ x ≤ x ⊓ y,
    apply le_inf,
    apply inf_le_right,
    apply inf_le_left,
  }
end
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := begin
  apply le_antisymm,
  { show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z),
    apply le_inf,
    { show x ⊓ y ⊓ z ≤ x,
      have h₀ : x ⊓ y ≤ x,  by apply inf_le_left,
      have h₁ : x ⊓ y ⊓ z ≤ x ⊓ y, by apply inf_le_left,
      apply le_trans h₁ h₀,
    },
    { show x ⊓ y ⊓ z ≤ y ⊓ z,
      have h₀ : x ⊓ y ⊓ z ≤ z, by apply inf_le_right, 
      have h₁ : x ⊓ y ⊓ z ≤ x ⊓ y, by apply inf_le_left,
      have h₂ : x ⊓ y ≤ y, by apply inf_le_right,
      have h₃ : x ⊓ y ⊓ z ≤ y, by apply le_trans h₁ h₂,  
      apply le_inf h₃ h₀,
    }
  },
  { show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z,
    apply le_inf,
    { show x ⊓ (y ⊓ z) ≤ x ⊓ y,
      apply le_inf,
      { show x ⊓ (y ⊓ z) ≤ x,
        apply inf_le_left,
      },
      { show x ⊓ (y ⊓ z) ≤ y,
        have h₀ : y ⊓ z ≤ y, apply inf_le_left,
        have h₁ : x ⊓ (y ⊓ z) ≤ y ⊓ z, apply inf_le_right, 
        apply le_trans h₁ h₀,
      }
    },
    { show x ⊓ (y ⊓ z) ≤ z,
      have h₀ : x ⊓ (y ⊓ z) ≤ y ⊓ z, apply inf_le_right,
      have h₁ : y ⊓ z ≤ z, apply inf_le_right, 
      apply le_trans h₀ h₁,
    },
  }
end

example : x ⊔ y = y ⊔ x := begin
  apply le_antisymm,
  { show x ⊔ y ≤ y ⊔ x,
    apply sup_le,
    { show x ≤ y ⊔ x,
      apply le_sup_right,
    },
    { show y ≤ y ⊔ x,
      apply le_sup_left,
    }
  },
  { show y ⊔ x ≤ x ⊔ y,
    have h₀ : y ≤ x ⊔ y, by apply le_sup_right, 
    have h₁ : x ≤ x ⊔ y, by apply le_sup_left, 
    apply sup_le h₀ h₁,
  },
end

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := begin
  apply le_antisymm,
  { show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z),
    apply sup_le,
    { show x ⊔ y ≤ x ⊔ (y ⊔ z),
      apply sup_le,
      { show x ≤ x ⊔ (y ⊔ z),
        apply le_sup_left,
      },
      { show y ≤ x ⊔ (y ⊔ z),
        have h₀ : y ≤ y ⊔ z, apply le_sup_left, 
        have h₁ : y ⊔ z ≤ x ⊔ (y ⊔ z) , apply le_sup_right, 
        apply le_trans h₀ h₁,
      }
    },
    { show z ≤ x ⊔ (y ⊔ z),
      have h₀ : z ≤ y ⊔ z, by apply le_sup_right, 
      have h₁ : y ⊔ z ≤ x ⊔ (y ⊔ z), by apply le_sup_right,
      apply le_trans h₀ h₁,
    }
  },
  { show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z,
    apply sup_le,
    { show x ≤ x ⊔ y ⊔ z,
      have h₀ : x ≤ x ⊔ y, by apply le_sup_left,
      have h₁ : x ⊔ y ≤ x ⊔ y ⊔ z, by apply le_sup_left, 
      apply le_trans h₀ h₁,
    },
    { show y ⊔ z ≤ x ⊔ y ⊔ z,
      apply sup_le,
      { show y ≤ x ⊔ y ⊔ z,
        have h₀ : y ≤ x ⊔ y, by apply le_sup_right,
        have h₁ : x ⊔ y ≤ x ⊔ y ⊔ z, by apply le_sup_left,
        apply le_trans h₀ h₁,    
      },
      { show z ≤ x ⊔ y ⊔ z,
        apply le_sup_right
      }
    },
  },
end

theorem absorb1 : x ⊓ (x ⊔ y) = x := begin
  apply le_antisymm,
  { show x ⊓ (x ⊔ y) ≤ x,
    apply inf_le_left,
  },
  { show x ≤ x ⊓ (x ⊔ y),
    have h₀ : x ≤ x ⊔ y, apply le_sup_left,
    have h₁ : x ≤ x, apply le_refl,  
    apply le_inf h₁ h₀,
  },
end

theorem absorb2 : x ⊔ (x ⊓ y) = x := begin
  apply le_antisymm,
  { show x ⊔ (x ⊓ y) ≤ x,
    have h₀ : x ≤ x, by apply le_refl, 
    have h₁ : x ⊓ y ≤ x, by apply inf_le_left, 
    apply sup_le h₀ h₁,
  },
  { show x ≤ x ⊔ (x ⊓ y),
    apply le_sup_left,
  },
end

end

section
variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

end

section
variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := begin

  have h₀ : (a ⊔ b) ⊓ (a ⊔ c) = ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c), by apply h,
  have h₁ : ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c) = a ⊔ ((a ⊔ b) ⊓ c), {
    rw inf_comm,
    rw absorb1 a b,
  },
  have h₂ : a ⊔ ((a ⊔ b) ⊓ c) = a ⊔ ((c ⊓ a) ⊔ (c ⊓ b)), {
    rw inf_comm,
    rw h,
  },
  have h₃ : a ⊔ ((c ⊓ a) ⊔ (c ⊓ b)) = a ⊔ (b ⊓ c), {
    rw inf_comm,
    nth_rewrite 0 ←sup_assoc,
    rw absorb2,
    rw inf_comm,
  },

  rw [h₀, h₁, h₂, h₃],
end

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := begin

  have h₀ : (a ⊓ b) ⊔ (a ⊓ c) = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c), by apply h,
  have h₁ : ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) = a ⊓ ((a ⊓ b) ⊔ c), by rw [sup_comm, absorb2],
  have h₂ : a ⊓ ((a ⊓ b) ⊔ c) = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)), by rw [sup_comm, h],
  have h₃ : a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) = a ⊓ (b ⊔ c), by rw [← inf_assoc, sup_comm, absorb1, sup_comm],

  rw [h₀, h₁, h₂, h₃],
end

end

section
variables {R : Type*} [ordered_ring R]
variables a b c : R

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example : a + -b = a - b := begin
  rw ← sub_eq_add_neg,
  -- refine eq.symm _,
end

example : a - a = 0 := begin
 exact sub_self a,
end

-- 이렇게 하는 게 맞을까?
example : a ≤ b → 0 ≤ b - a := begin
  assume h : a ≤ b, 
  have h₀ : -a + a ≤ -a + b, begin
    apply add_le_add_left h,
  end,
  have h₁ : a - a ≤ b - a, begin
    rw add_comm at h₀,
    nth_rewrite_rhs 0 add_comm at h₀,
    rw ← sub_eq_add_neg at h₀,
    rw ← sub_eq_add_neg at h₀,
    exact h₀,
  end,
  have h₂ : 0 ≤ b - a, begin
    rw sub_self at h₁, 
    exact h₁,
  end,
  exact h₂,
end

example : a - b + c = a + c - b := begin
exact sub_add_eq_add_sub a b c,
end

example : 0 ≤ b - a → a ≤ b := begin
  assume h : 0 ≤ b - a,
  have h₀ : a - a ≤ b - a, begin
    rw ← sub_self at h,
    exact h,
  end,
  have h₁ : a - a + a ≤ b - a + a, begin
    apply add_le_add_right,
    exact h₀,
  end,
  have h₂ : a ≤ b, begin
    rw sub_self at h₁,
    rw sub_eq_add_neg at h₁,
    nth_rewrite_rhs 0 add_assoc at h₁,
    rw add_left_neg at h₁,
    rw add_zero at h₁,
    rw zero_add at h₁,
    exact h₁,
  end, 
  exact h₂,
end

example : -a + a = 0 := begin
exact neg_add_self a,
end

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := begin
  have h₀ : 0 ≤ b - a, begin
    rw ← sub_self a,
    rw sub_eq_add_neg,
    rw sub_eq_add_neg,
    apply add_le_add_right h,
  end,
  have h₁ : 0 ≤ (b - a) * c, begin
    apply mul_nonneg,
    apply h₀,
    apply h',
  end,
  have h₂ : 0 ≤ b * c - a * c, begin
    rw sub_mul at h₁,
    exact h₁
  end,   
  have h₃ : a * c ≤ b * c, begin
    have j₀ : 0 + a * c ≤ b * c - a * c + a * c, by apply add_le_add_right h₂,
    rw zero_add at j₀,
    rw sub_eq_add_neg at j₀,
    rw add_assoc at j₀,
    rw neg_add_self (a * c) at j₀,
    rw add_zero at j₀,
    exact j₀,
  end,
  exact h₃,
end

example : a + a = 2 * a := begin
library_search,
-- sorry,
end


end

section
variables {X : Type*} [metric_space X]
variables x y z : X

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check nonneg_of_mul_nonneg_left
-- (h : 0 ≤ a * b) (h1 : 0 < a) : 0 ≤ b :=
example (x y : X) : 0 ≤ dist x y := begin
  have h₀ : dist x x ≤ dist x y + dist y x, by apply dist_triangle,
  have h₁ : dist x x ≤ dist x y + dist x y, { nth_rewrite_rhs 1 dist_comm at h₀, exact h₀ }, 
  have h₂ : 0 ≤ 2 * (dist x y), {
    rw dist_self at h₁,
    rw two_mul,
    exact h₁,
  },
  apply nonneg_of_mul_nonneg_left h₂,
  linarith,
end

end

