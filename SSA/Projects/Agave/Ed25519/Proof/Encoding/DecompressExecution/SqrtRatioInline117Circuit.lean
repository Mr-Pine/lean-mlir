import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineSerializerRename

namespace Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Encoding.RIR
open ToBytes
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option pp.maxSteps 5000

def prepared (E : ⟪ToBytes.program.Γ⟫) (a : (Fin 5 → BitVec 64)) : ⟪ToBytes.program.Γ⟫ :=
  E[%0 := .value 8#64,
    %1 := .value 16#64,
    %2 := .value 24#64,
    %3 := .value 32#64,
    %4 := .value 51#64,
    %5 := .value 2251799813685247#64,
    %6 := .value 19#64,
    %7 := .value 1#64,
    %8 := .value 2#64,
    %9 := .value 3#64,
    %10 := .value 4#64,
    %11 := .value 40#64,
    %12 := .value 5#64,
    %13 := .value 48#64,
    %14 := .value 7#64,
    %15 := .value 6#64,
    %16 := .value 13#64,
    %17 := .value 21#64,
    %18 := .value 9#64,
    %19 := .value 29#64,
    %20 := .value 10#64,
    %21 := .value 37#64,
    %22 := .value 11#64,
    %23 := .value 45#64,
    %24 := .value 12#64,
    %25 := .value 14#64,
    %26 := .value 18#64,
    %27 := .value 15#64,
    %28 := .value 26#64,
    %29 := .value 34#64,
    %30 := .value 17#64,
    %31 := .value 42#64,
    %32 := .value 50#64,
    %33 := .value 20#64,
    %34 := .value 23#64,
    %35 := .value 22#64,
    %36 := .value 31#64,
    %37 := .value 39#64,
    %38 := .value 47#64,
    %39 := .value 25#64,
    %40 := .value 27#64,
    %41 := .value 28#64,
    %42 := .value 36#64,
    %43 := .value 30#64,
    %44 := .value 44#64,
    %45 := .value (a 0), %47 := .value (a 1), %49 := .value (a 2), %51 := .value (a 3), %53 := .value (a 4)]

def byteRegister : Fin 32 → Reg ToBytes.program.Γ (.bv 8) :=
  ![(%94),(%97),(%100),(%103),(%106),(%109),(%115),(%118),(%121),(%124),(%127),(%130),(%135),(%138),(%141),(%144),(%147),(%150),(%153),(%158),(%161),(%164),(%167),(%170),(%173),(%178),(%181),(%184),(%187),(%190),(%193),(%196)]

attribute [-simp] BitVec.shiftLeft_add_distrib in
theorem tail54 (E : ⟪ToBytes.program.Γ⟫) (r p : Pointer) (a : (Fin 5 → BitVec 64))
    (s S : GlobalState) (hS : S = s) (hwf : S.WF)
    (hr : SmallRange S.mem r 32)
    (hEargs : E.args = (ToBytes.program.args (.value r) (.value p)).get) :
    ∃ E', ToBytes.program.entry.runBodyFrom (prepared E a) 54 S =
      .value (E', { s with mem := ToBytes.storeBytes s.mem r (ToBytes.machine a) }) ∧
      (∀ i, E'.read (byteRegister i) = .value (ToBytes.machine a i)) := by
  have hr0 := hr.fits_add (k := 0) (count := 1) (by decide)
  have hr1 := hr.fits_add (k := 1) (count := 1) (by decide)
  have hr2 := hr.fits_add (k := 2) (count := 1) (by decide)
  have hr3 := hr.fits_add (k := 3) (count := 1) (by decide)
  have hr4 := hr.fits_add (k := 4) (count := 1) (by decide)
  have hr5 := hr.fits_add (k := 5) (count := 1) (by decide)
  have hr6 := hr.fits_add (k := 6) (count := 1) (by decide)
  have hr7 := hr.fits_add (k := 7) (count := 1) (by decide)
  have hr8 := hr.fits_add (k := 8) (count := 1) (by decide)
  have hr9 := hr.fits_add (k := 9) (count := 1) (by decide)
  have hr10 := hr.fits_add (k := 10) (count := 1) (by decide)
  have hr11 := hr.fits_add (k := 11) (count := 1) (by decide)
  have hr12 := hr.fits_add (k := 12) (count := 1) (by decide)
  have hr13 := hr.fits_add (k := 13) (count := 1) (by decide)
  have hr14 := hr.fits_add (k := 14) (count := 1) (by decide)
  have hr15 := hr.fits_add (k := 15) (count := 1) (by decide)
  have hr16 := hr.fits_add (k := 16) (count := 1) (by decide)
  have hr17 := hr.fits_add (k := 17) (count := 1) (by decide)
  have hr18 := hr.fits_add (k := 18) (count := 1) (by decide)
  have hr19 := hr.fits_add (k := 19) (count := 1) (by decide)
  have hr20 := hr.fits_add (k := 20) (count := 1) (by decide)
  have hr21 := hr.fits_add (k := 21) (count := 1) (by decide)
  have hr22 := hr.fits_add (k := 22) (count := 1) (by decide)
  have hr23 := hr.fits_add (k := 23) (count := 1) (by decide)
  have hr24 := hr.fits_add (k := 24) (count := 1) (by decide)
  have hr25 := hr.fits_add (k := 25) (count := 1) (by decide)
  have hr26 := hr.fits_add (k := 26) (count := 1) (by decide)
  have hr27 := hr.fits_add (k := 27) (count := 1) (by decide)
  have hr28 := hr.fits_add (k := 28) (count := 1) (by decide)
  have hr29 := hr.fits_add (k := 29) (count := 1) (by decide)
  have hr30 := hr.fits_add (k := 30) (count := 1) (by decide)
  have hr31 := hr.fits_add (k := 31) (count := 1) (by decide)
  simp only [Pointer.add_zero] at hr0
  have hs := toBytesSafe3 (a 0) (a 1) (a 2) (a 3) (a 4)
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩
  dsimp only [prepared]
  seal_env
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure [h0, h1]
  step_pure [h2, h3]
  step_pure [h4, h5]
  step_pure [h6, h7]
  step_pure [h8, h9]
  step_pure [h10, h11]
  step_pure [h12, h13]
  step_pure
  step_pure [h14, h15]
  step_pure
  step_pure [h16, h17]
  step_pure
  step_pure [h18, h19]
  step_pure
  step_pure [h20, h21]
  step_pure
  step_pure [h22, h23]
  step_pure [h24, h25]
  step_pure
  step_pure [h26, h27]
  step_pure
  step_pure [h28, h29]
  step_pure
  step_pure
  step_pure [h30, h31]
  step_pure
  step_pure
  step_pure [h32, h33]
  step_pure
  step_pure
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure
  step_pure [masked_shift_3_signed, masked_shift_3_unsigned]
  step_pure [boundary_disjoint_3]
  have hgep := hr.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure [masked_shift_6_signed, masked_shift_6_unsigned]
  step_pure [boundary_disjoint_6]
  have hgep := hr.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure [masked_shift_1_signed, masked_shift_1_unsigned]
  step_pure [boundary_disjoint_1]
  have hgep := hr.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  step_pure [masked_shift_4_signed, masked_shift_4_unsigned]
  step_pure [boundary_disjoint_4]
  have hgep := hr.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure
  step_store
  step_pure
  have hgep := hr.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_pure [last_byte_trunc_signed, last_byte_trunc_unsigned]
  step_store
  rw [BasicBlock.runBodyFrom_done (by decide +kernel)]
  simp only [EffectM.pure_eq, PoisonOr.value_inj, Prod.mk.injEq]
  refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
  · rw [hS]
    subst_vars
    simp [ToBytes.machine, ToBytes.carryMachine, ToBytes.reverseCarry,
      ToBytes.quotientCarry, weakWord, ToBytes.rawBytes, ToBytes.storeBytes, Pointer.add]
  · intro i
    fin_cases i <;> subst_vars <;>
      simp [byteRegister, ToBytes.machine, ToBytes.carryMachine, ToBytes.reverseCarry,
        ToBytes.quotientCarry, weakWord, ToBytes.rawBytes, mlir_env]

end Agave.Ed25519.Encoding.Decompress.Execution.SerializerRename
