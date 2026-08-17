import SSA.Projects.Firedancer.Limbs

namespace R43x6
def limbWidth := 64
def baseBits := 43
def limbCount := 6
def decode := LimbRepresentations.decode limbWidth baseBits limbCount
def decode' := decode ∘ (λ (v: LimbRepresentations.Limbs 64 8) => v.take limbCount)
end R43x6
