import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Init
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Iteration

/-! The thirty fresh allocations in the original AVX2 entry block. All
scratch ranges and separation from caller allocations follow from `WF`. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

/-- Allocation sizes in the exact order of registers 237 through 266. -/
def avx2StackSize (i : Nat) : Nat :=
  if i < 20 then 160 else
  if i < 22 then 40 else
  if i < 27 then 160 else
  if i = 27 then 1280 else
  if i < 30 then 256 else 0

def avx2Stack (s : GlobalState) : Nat → GlobalState
  | 0 => s
  | n + 1 => (avx2Stack s n).alloca (avx2StackSize n)

def avx2StackPtr (s : GlobalState) (n : Nat) : Pointer := (avx2Stack s n).allocaPtr

theorem avx2Stack_wf (hwf : s.WF) (n : Nat) : (avx2Stack s n).WF := by
  induction n with
  | zero => exact hwf
  | succ n ih => exact ih.alloca

theorem avx2Stack_existing (hwf : s.WF) (h : Buffer s.mem q bytes) (n : Nat) :
    Buffer (avx2Stack s n).mem q bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca_existing (avx2Stack_wf hwf n) _

theorem avx2Stack_read_existing (hwf : s.WF) (h : Buffer s.mem q bytes)
    (n bits : Nat) : (avx2Stack s n).mem.readAt q bits = s.mem.readAt q bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((avx2Stack s n).alloca _).mem.readAt q bits = _
    rw [MemoryState.readAt_alloca (avx2Stack_wf hwf n)
      (avx2Stack_existing hwf h n).fits, ih]

theorem avx2Stack_buffer (hwf : s.WF) (i n : Nat) (hi : i < n)
    (hsize : avx2StackSize i < 2 ^ 63) :
    Buffer (avx2Stack s n).mem (avx2StackPtr s i) (avx2StackSize i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : i = n
    · subst i
      exact Buffer.alloca _ _ hsize
    · exact (ih (by omega)).alloca_existing (avx2Stack_wf hwf n) _

theorem avx2Stack_separate_caller (hwf : s.WF) (h : Buffer s.mem q bytes)
    (n : Nat) : (avx2StackPtr s n).id ≠ q.id :=
  (GlobalState.ne_allocaPtr_of_fits (avx2Stack_wf hwf n)
    (avx2Stack_existing hwf h n).fits).symm

theorem avx2Stack_nextFreeBlock (s : GlobalState) (n : Nat) :
    (avx2Stack s n).alloc.nextFreeBlock = s.alloc.nextFreeBlock + n := by
  induction n with
  | zero => simp [avx2Stack]
  | succ n ih => simp [avx2Stack, GlobalState.alloca, ih, Nat.add_assoc]

theorem avx2Stack_separate (s : GlobalState) (i j : Nat) (hne : i ≠ j) :
    (avx2StackPtr s i).id ≠ (avx2StackPtr s j).id := by
  intro heq
  have hv := congrArg (fun id => id.id) heq
  simp only [avx2StackPtr, GlobalState.allocaPtr_id_id, avx2Stack_nextFreeBlock] at hv
  omega

theorem avx2Stack_zero (hwf : s.WF) (i n bits : Nat) (hi : i < n)
    (hsize : avx2StackSize i < 2 ^ 63) :
    (avx2Stack s n).mem.readAt (avx2StackPtr s i) bits = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : i = n
    · subst i
      simp [avx2Stack, avx2StackPtr, MemoryState.readAt, GlobalState.alloca,
        GlobalState.allocaPtr, MemoryState.getElem?_eq, Pointer.offsetInBits]
    · change ((avx2Stack s n).alloca _).mem.readAt (avx2StackPtr s i) bits = 0
      rw [MemoryState.readAt_alloca (avx2Stack_wf hwf n)
        (avx2Stack_buffer hwf i n (by omega) hsize).fits]
      exact ih (by omega)

private theorem modifyGet_run {α : Type} (f : GlobalState → α × GlobalState)
    (s : GlobalState) : (modifyGet f : EffectM α) s = .value (f s) := rfl

private theorem write_congr {Γ : Ctx} {E E' : ⟪Γ⟫} {t : Ty}
    {d : Dst Γ t} {v v' : ⟦t⟧}
    (hE : E = E') (hv : v = v') : E.write d v = E'.write d v' := by
  cases hE
  cases hv
  rfl

/-- Exact entry-register values, including the compiler's partial-poison
vector constants. No undefined lane is replaced with an arbitrary value. -/
def avx2EntryEnv (E : ⟪avx2Kernel.Γ⟫) (g : Avx2CFG.Globals)
    (s : GlobalState) : ⟪avx2Kernel.Γ⟫ :=
  E[
    %0 := .value 1#32,
    %1 := .value 0#8,
    %2 := .value 256#64,
    %3 := .value 32#64,
    %4 := .value 0#64,
    %5 := .value 6#64,
    %6 := .value 63#64,
    %7 := .value 59#64,
    %8 := .value 8#64,
    %9 := .value 31#64,
    %10 := .value 1#64,
    %11 := .value 15#64,
    %12 := .value 224#8,
    %13 := .value 5#64,
    %14 := .value 251#64,
    %15 := .value 56#64,
    %16 := .value 255#64,
    %17 := .value 127#64,
    %18 := .value 248#64,
    %19 := .value 18446744073709551615#64,
    %20 := .value 64#64,
    %21 := .value 96#64,
    %22 := .value 128#64,
    %23 := .value 0#32,
    %24 := #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .value 0#32, .value 0#32, .value 0#32, .value 0#32],
    %25 := #v[.value 0#32, .value 1#32, .value 0#32, .value 0#32, .value 1#32, .value 0#32, .value 0#32, .value 0#32],
    %26 := (Ty.vec 8 32).poisoned,
    %27 := #v[.value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32, .value 1#32],
    %28 := .poison,
    %29 := (Ty.vec 8 32).poisoned,
    %30 := .value 0#32,
    %31 := #v[.value 0#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %32 := .value 1#32,
    %33 := #v[.value 0#32, .value 0#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %34 := .value 2#32,
    %35 := #v[.value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison, .poison],
    %36 := .value 3#32,
    %37 := #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison],
    %38 := .value 4#32,
    %39 := #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison],
    %40 := .value 5#32,
    %41 := #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison],
    %42 := .value 6#32,
    %43 := #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison],
    %44 := .value 7#32,
    %45 := #v[.value 0#32, .value 0#32, .value 0#32, .value 0#32, .poison, .poison, .poison, .poison],
    %46 := (Ty.vec 8 32).poisoned,
    %47 := .value 0#32,
    %48 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %49 := .value 1#32,
    %50 := #v[.poison, .value 0#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %51 := .value 2#32,
    %52 := #v[.poison, .value 0#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %53 := .value 3#32,
    %54 := #v[.poison, .value 0#32, .poison, .value 0#32, .poison, .poison, .poison, .poison],
    %55 := .value 4#32,
    %56 := #v[.poison, .value 0#32, .poison, .value 0#32, .value 0#32, .poison, .poison, .poison],
    %57 := .value 5#32,
    %58 := #v[.poison, .value 0#32, .poison, .value 0#32, .value 0#32, .poison, .poison, .poison],
    %59 := .value 6#32,
    %60 := #v[.poison, .value 0#32, .poison, .value 0#32, .value 0#32, .poison, .value 0#32, .poison],
    %61 := .value 7#32,
    %62 := #v[.poison, .value 0#32, .poison, .value 0#32, .value 0#32, .poison, .value 0#32, .poison],
    %63 := .value 67108862#32,
    %64 := .value 134217690#32,
    %65 := (Ty.vec 8 32).poisoned,
    %66 := .value 0#32,
    %67 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %68 := .value 1#32,
    %69 := #v[.poison, .value 134217690#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %70 := .value 2#32,
    %71 := #v[.poison, .value 134217690#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %72 := .value 3#32,
    %73 := #v[.poison, .value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison],
    %74 := .value 4#32,
    %75 := #v[.poison, .value 134217690#32, .poison, .value 67108862#32, .value 134217690#32, .poison, .poison, .poison],
    %76 := .value 5#32,
    %77 := #v[.poison, .value 134217690#32, .poison, .value 67108862#32, .value 134217690#32, .poison, .poison, .poison],
    %78 := .value 6#32,
    %79 := #v[.poison, .value 134217690#32, .poison, .value 67108862#32, .value 134217690#32, .poison, .value 67108862#32, .poison],
    %80 := .value 7#32,
    %81 := #v[.poison, .value 134217690#32, .poison, .value 67108862#32, .value 134217690#32, .poison, .value 67108862#32, .poison],
    %82 := .value 134217726#32,
    %83 := (Ty.vec 8 32).poisoned,
    %84 := .value 0#32,
    %85 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %86 := .value 1#32,
    %87 := #v[.poison, .value 134217726#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %88 := .value 2#32,
    %89 := #v[.poison, .value 134217726#32, .poison, .poison, .poison, .poison, .poison, .poison],
    %90 := .value 3#32,
    %91 := #v[.poison, .value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison],
    %92 := .value 4#32,
    %93 := #v[.poison, .value 134217726#32, .poison, .value 67108862#32, .value 134217726#32, .poison, .poison, .poison],
    %94 := .value 5#32,
    %95 := #v[.poison, .value 134217726#32, .poison, .value 67108862#32, .value 134217726#32, .poison, .poison, .poison],
    %96 := .value 6#32,
    %97 := #v[.poison, .value 134217726#32, .poison, .value 67108862#32, .value 134217726#32, .poison, .value 67108862#32, .poison],
    %98 := .value 7#32,
    %99 := #v[.poison, .value 134217726#32, .poison, .value 67108862#32, .value 134217726#32, .poison, .value 67108862#32, .poison],
    %100 := (Ty.vec 8 32).poisoned,
    %101 := .value 0#32,
    %102 := #v[.value 0#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %103 := .value 1#32,
    %104 := #v[.value 0#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %105 := .value 2#32,
    %106 := #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .poison, .poison, .poison],
    %107 := .value 3#32,
    %108 := #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .poison, .poison, .poison],
    %109 := .value 4#32,
    %110 := #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .poison, .poison, .poison],
    %111 := .value 5#32,
    %112 := #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .value 0#32, .poison, .poison],
    %113 := .value 6#32,
    %114 := #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .value 0#32, .poison, .poison],
    %115 := .value 7#32,
    %116 := #v[.value 0#32, .poison, .value 0#32, .poison, .poison, .value 0#32, .poison, .value 0#32],
    %117 := .value 16#8,
    %118 := .value g.address0,
    %119 := (Ty.vec 8 32).poisoned,
    %120 := .value 0#32,
    %121 := #v[.value 134217690#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %122 := .value 1#32,
    %123 := #v[.value 134217690#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %124 := .value 2#32,
    %125 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %126 := .value 3#32,
    %127 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %128 := .value 4#32,
    %129 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %130 := .value 5#32,
    %131 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %132 := .value 6#32,
    %133 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %134 := .value 7#32,
    %135 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %136 := (Ty.vec 8 32).poisoned,
    %137 := .value 0#32,
    %138 := #v[.value 134217726#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %139 := .value 1#32,
    %140 := #v[.value 134217726#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %141 := .value 2#32,
    %142 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %143 := .value 3#32,
    %144 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %145 := .value 4#32,
    %146 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %147 := .value 5#32,
    %148 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %149 := .value 6#32,
    %150 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %151 := .value 7#32,
    %152 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %153 := .value 160#64,
    %154 := (Ty.vec 8 32).poisoned,
    %155 := .value 0#32,
    %156 := #v[.value 134217690#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %157 := .value 1#32,
    %158 := #v[.value 134217690#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %159 := .value 2#32,
    %160 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %161 := .value 3#32,
    %162 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %163 := .value 4#32,
    %164 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .value 134217690#32, .poison, .poison, .poison],
    %165 := .value 5#32,
    %166 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .value 134217690#32, .poison, .poison, .poison],
    %167 := .value 6#32,
    %168 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .value 134217690#32, .poison, .value 67108862#32, .poison],
    %169 := .value 7#32,
    %170 := #v[.value 134217690#32, .poison, .value 67108862#32, .poison, .value 134217690#32, .poison, .value 67108862#32, .poison],
    %171 := (Ty.vec 8 32).poisoned,
    %172 := .value 0#32,
    %173 := #v[.value 134217726#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %174 := .value 1#32,
    %175 := #v[.value 134217726#32, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %176 := .value 2#32,
    %177 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %178 := .value 3#32,
    %179 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .poison, .poison, .poison, .poison],
    %180 := .value 4#32,
    %181 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .value 134217726#32, .poison, .poison, .poison],
    %182 := .value 5#32,
    %183 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .value 134217726#32, .poison, .poison, .poison],
    %184 := .value 6#32,
    %185 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .value 134217726#32, .poison, .value 67108862#32, .poison],
    %186 := .value 7#32,
    %187 := #v[.value 134217726#32, .poison, .value 67108862#32, .poison, .value 134217726#32, .poison, .value 67108862#32, .poison],
    %188 := (Ty.vec 8 32).poisoned,
    %189 := .value 0#32,
    %190 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %191 := .value 1#32,
    %192 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %193 := .value 2#32,
    %194 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %195 := .value 3#32,
    %196 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %197 := .value 4#32,
    %198 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %199 := .value 5#32,
    %200 := #v[.poison, .poison, .poison, .poison, .poison, .value 134217690#32, .poison, .poison],
    %201 := .value 6#32,
    %202 := #v[.poison, .poison, .poison, .poison, .poison, .value 134217690#32, .poison, .poison],
    %203 := .value 7#32,
    %204 := #v[.poison, .poison, .poison, .poison, .poison, .value 134217690#32, .poison, .value 67108862#32],
    %205 := (Ty.vec 8 32).poisoned,
    %206 := .value 0#32,
    %207 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %208 := .value 1#32,
    %209 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %210 := .value 2#32,
    %211 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %212 := .value 3#32,
    %213 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %214 := .value 4#32,
    %215 := #v[.poison, .poison, .poison, .poison, .poison, .poison, .poison, .poison],
    %216 := .value 5#32,
    %217 := #v[.poison, .poison, .poison, .poison, .poison, .value 134217726#32, .poison, .poison],
    %218 := .value 6#32,
    %219 := #v[.poison, .poison, .poison, .poison, .poison, .value 134217726#32, .poison, .poison],
    %220 := .value 7#32,
    %221 := #v[.poison, .poison, .poison, .poison, .poison, .value 134217726#32, .poison, .value 67108862#32],
    %222 := .value 255#8,
    %223 := .value g.address1,
    %224 := .value g.address2,
    %225 := .value 7#64,
    %226 := .value 4#64,
    %227 := .value 3#64,
    %228 := .value 26#64,
    %229 := #v[.value 26#64, .value 26#64],
    %230 := .value 16#64,
    %231 := #v[.value 26#64, .value 26#64, .value 26#64, .value 26#64],
    %232 := .value 72#64,
    %233 := .value 2#64,
    %234 := .value 104#64,
    %235 := .value 136#64,
    %236 := .value 152#64,
    %237 := .value (avx2StackPtr s 0),
    %238 := .value (avx2StackPtr s 1),
    %239 := .value (avx2StackPtr s 2),
    %240 := .value (avx2StackPtr s 3),
    %241 := .value (avx2StackPtr s 4),
    %242 := .value (avx2StackPtr s 5),
    %243 := .value (avx2StackPtr s 6),
    %244 := .value (avx2StackPtr s 7),
    %245 := .value (avx2StackPtr s 8),
    %246 := .value (avx2StackPtr s 9),
    %247 := .value (avx2StackPtr s 10),
    %248 := .value (avx2StackPtr s 11),
    %249 := .value (avx2StackPtr s 12),
    %250 := .value (avx2StackPtr s 13),
    %251 := .value (avx2StackPtr s 14),
    %252 := .value (avx2StackPtr s 15),
    %253 := .value (avx2StackPtr s 16),
    %254 := .value (avx2StackPtr s 17),
    %255 := .value (avx2StackPtr s 18),
    %256 := .value (avx2StackPtr s 19),
    %257 := .value (avx2StackPtr s 20),
    %258 := .value (avx2StackPtr s 21),
    %259 := .value (avx2StackPtr s 22),
    %260 := .value (avx2StackPtr s 23),
    %261 := .value (avx2StackPtr s 24),
    %262 := .value (avx2StackPtr s 25),
    %263 := .value (avx2StackPtr s 26),
    %264 := .value (avx2StackPtr s 27),
    %265 := .value (avx2StackPtr s 28),
    %266 := .value (avx2StackPtr s 29),
    %267 := .value ((avx2StackPtr s 21).add 32#64),
    %268 := .value 0#64,
    %269 := .value 0#64]

set_option maxHeartbeats 2000000 in
/-- The complete imported entry block: constants, thirty allocations, zero
NAF output, padded scalar copy, and initial zero cursor/carry. -/
theorem avx2_entry_block (E : ⟪avx2Kernel.Γ⟫) (g : Avx2CFG.Globals)
    (s : GlobalState) (input : Pointer) (scalar : BitVec 256) (hwf : s.WF)
    (hinput : Buffer s.mem input 32) (hscalar : s.mem.readAt input 256 = scalar)
    (harg : E.args 1 = .value input) :
    (avx2Kernel.bb0 g).run avx2Kernel.blockParams E s =
      .value ((avx2EntryEnv E g s, .inr 1),
        nafInitialized (avx2Stack s 30) (avx2StackPtr s 29) (avx2StackPtr s 21) scalar) := by
  have hdigits : Buffer (avx2Stack s 30).mem (avx2StackPtr s 29) 256 :=
    avx2Stack_buffer hwf 29 30 (by decide) (by decide)
  have hscratch : Buffer (avx2Stack s 30).mem (avx2StackPtr s 21) 40 :=
    avx2Stack_buffer hwf 21 30 (by decide) (by decide)
  have hzero (env : ⟪avx2Kernel.Γ⟫) := NAF.Memory.zero_digits hdigits env
  have hscale : Operation.gepInboundsIndex 1 (.value 32#64) = .value (32 : Int) := by
    decide +kernel
  have hgep := (hscratch.storeAt (avx2StackPtr s 29) (0 : BitVec 2048)).gep 32 (by decide)
  simp only [Int.cast_ofNat_Int] at hgep
  have hfits := (hscratch.storeAt (avx2StackPtr s 29) (0 : BitVec 2048)).fits_at 32 8 (by decide)
  have hstore (env : ⟪avx2Kernel.Γ⟫) :
      Operation.store (τ := .bv 64) (.value ((avx2StackPtr s 21).add 32#64)) (.value 0#64) env
        (nafCleared (avx2Stack s 30) (avx2StackPtr s 29)) =
          .value (env, nafPadded (avx2Stack s 30) (avx2StackPtr s 29) (avx2StackPtr s 21)) :=
    run_store (env := env) hfits rfl
  have hread : (avx2Stack s 30).mem.readAt input 256 = scalar := by
    rw [avx2Stack_read_existing hwf hinput, hscalar]
  have hcopy (env : ⟪avx2Kernel.Γ⟫) := nafSetup_copy env (avx2Stack s 30)
    (avx2StackPtr s 29) (avx2StackPtr s 21) input scalar hscratch
    (avx2Stack_existing hwf hinput 30) (avx2Stack_separate_caller hwf hinput 29)
    (avx2Stack_separate_caller hwf hinput 21) hread
  simp [avx2Stack, avx2StackSize, avx2StackPtr, nafCleared] at hzero hgep hstore hcopy
  simp (config := {maxSteps := 1000000}) [BasicBlock.run, avx2Kernel.bb0, avx2EntryEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, TernOp.compute,
    Operation.insertelement, Ty.wrap, Ty.poisoned, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    modifyGet_run, harg, hzero, hscale, hgep, hstore, hcopy,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    avx2Stack, avx2StackSize, avx2StackPtr, nafCleared]
  repeat' apply write_congr
  all_goals first | rfl | decide +kernel


/-- The first cursor-forwarding block is part of the actual entry path. -/
theorem avx2_entry_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (input : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (hscalar : s.mem.readAt input 256 = scalar) (harg : E.args 1 = .value input) :
    (avx2Kernel p g).runFrom E 0 s =
      (avx2Kernel p g).runFrom ((avx2EntryEnv E g s)[%270 := .value 0#64]) 2
        (nafInitialized (avx2Stack s 30) (avx2StackPtr s 29)
          (avx2StackPtr s 21) scalar) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 0 = avx2Kernel.bb0 g from rfl,
    avx2_entry_block E g s input scalar hwf hinput hscalar harg]
  change (avx2Kernel p g).runFrom (avx2EntryEnv E g s) 1 _ = _
  rw [carry5_run]
  simp [avx2EntryEnv, mlir_env]

theorem avx2EntryEnv_loop (E : ⟪avx2Kernel.Γ⟫) (g : Avx2CFG.Globals)
    (s : GlobalState) :
    loopEnv5 ((avx2EntryEnv E g s)[%270 := .value 0#64]) (avx2StackPtr s 21) 0 0 =
      (avx2EntryEnv E g s)[%270 := .value 0#64] := by
  apply loopEnv5_of_reads <;> simp [avx2EntryEnv, mlir_env]

end Agave.Ed25519.DoubleBase.ExecutionAvx2
