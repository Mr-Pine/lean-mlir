import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk5
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk6
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk7

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem shifted_carry_bound (word : BitVec 128) (h : word.toNat < 2 ^ 120) :
    (word >>> 52).toNat < 2 ^ 110 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  norm_num at h ⊢
  omega

theorem cancellationCarry_bound (word : BitVec 128) (h : word.toNat < 2 ^ 120) :
    (cancellationCarry word).toNat < 2 ^ 110 := by
  have hb := cancellation_sum_bound word h
  obtain ⟨_, _, hn⟩ := product_add_flags
    ((cancellationDigit word).setWidth 128 * 671914833335277#128) word hb
  rw [cancellationCarry, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hn]
  exact (Nat.div_lt_iff_lt_mul (by decide)).2 (hb.trans (by decide))

def carryGapSum0 (d0 : BitVec 64) (u182 u229 : BitVec 128) : BitVec 128 :=
  let v230 : BitVec 128 := (d0.setWidth 128) * 3916664325105025#128
  let v231 : BitVec 128 := v230 + u182
  let v232 : BitVec 128 := v231 + u229
  v232

theorem carryGapSum0_bound (d0 : BitVec 64) (u182 u229 : BitVec 128)
    (hd226 : d0.toNat < 2 ^ 52)
    (hu182 : u182.toNat < 2 ^ 110)
    (hu229 : u229.toNat < 2 ^ 110)
    : (carryGapSum0 d0 u182 u229).toNat < 2 ^ 120 := by
  let v230 : BitVec 128 := (d0.setWidth 128) * 3916664325105025#128
  obtain ⟨h230u, h230s, h230n⟩ := product_constant_flags d0 3916664325105025#128 hd226 (by decide)
  let v231 : BitVec 128 := v230 + u182
  have h231bound : (v230).toNat + (u182).toNat < 2 ^ 120 := by
    simp only [v230, v231, h230n]
    norm_num at hd226 hu182 hu229 ⊢
    omega
  obtain ⟨h231u, h231s, h231n⟩ := product_add_flags (v230) (u182)
    (h231bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v230, v231] at h231u h231s h231n
  let v232 : BitVec 128 := v231 + u229
  have h232bound : (v231).toNat + (u229).toNat < 2 ^ 120 := by
    simp only [v230, v231, v232, h230n, h231n]
    norm_num at hd226 hu182 hu229 ⊢
    omega
  obtain ⟨h232u, h232s, h232n⟩ := product_add_flags (v231) (u229)
    (h232bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v230, v231, v232] at h232u h232s h232n
  change v232.toNat < 2 ^ 120
  rw [h232n]
  exact h232bound

def carryGapSum1 (d0 d1 : BitVec 64) (u188 u239 : BitVec 128) : BitVec 128 :=
  let v240 : BitVec 128 := (d0.setWidth 128) * 1367801#128
  let v241 : BitVec 128 := (d1.setWidth 128) * 3916664325105025#128
  let v242 : BitVec 128 := u188 + v240
  let v243 : BitVec 128 := v242 + v241
  let v244 : BitVec 128 := v243 + u239
  v244

theorem carryGapSum1_bound (d0 d1 : BitVec 64) (u188 u239 : BitVec 128)
    (hd226 : d0.toNat < 2 ^ 52)
    (hd236 : d1.toNat < 2 ^ 52)
    (hu188 : u188.toNat < 2 ^ 110)
    (hu239 : u239.toNat < 2 ^ 110)
    : (carryGapSum1 d0 d1 u188 u239).toNat < 2 ^ 120 := by
  let v240 : BitVec 128 := (d0.setWidth 128) * 1367801#128
  obtain ⟨h240u, h240s, h240n⟩ := product_constant_flags d0 1367801#128 hd226 (by decide)
  let v241 : BitVec 128 := (d1.setWidth 128) * 3916664325105025#128
  obtain ⟨h241u, h241s, h241n⟩ := product_constant_flags d1 3916664325105025#128 hd236 (by decide)
  let v242 : BitVec 128 := u188 + v240
  have h242bound : (u188).toNat + (v240).toNat < 2 ^ 120 := by
    simp only [v240, v241, v242, h240n, h241n]
    norm_num at hd226 hd236 hu188 hu239 ⊢
    omega
  obtain ⟨h242u, h242s, h242n⟩ := product_add_flags (u188) (v240)
    (h242bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v240, v241, v242] at h242u h242s h242n
  let v243 : BitVec 128 := v242 + v241
  have h243bound : (v242).toNat + (v241).toNat < 2 ^ 120 := by
    simp only [v240, v241, v242, v243, h240n, h241n, h242n]
    norm_num at hd226 hd236 hu188 hu239 ⊢
    omega
  obtain ⟨h243u, h243s, h243n⟩ := product_add_flags (v242) (v241)
    (h243bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v240, v241, v242, v243] at h243u h243s h243n
  let v244 : BitVec 128 := v243 + u239
  have h244bound : (v243).toNat + (u239).toNat < 2 ^ 120 := by
    simp only [v240, v241, v242, v243, v244, h240n, h241n, h242n, h243n]
    norm_num at hd226 hd236 hu188 hu239 ⊢
    omega
  obtain ⟨h244u, h244s, h244n⟩ := product_add_flags (v243) (u239)
    (h244bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v240, v241, v242, v243, v244] at h244u h244s h244n
  change v244.toNat < 2 ^ 120
  rw [h244n]
  exact h244bound

def carryGapSum2 (d1 d2 : BitVec 64) (u196 u251 : BitVec 128) : BitVec 128 :=
  let v252 : BitVec 128 := (d1.setWidth 128) * 1367801#128
  let v253 : BitVec 128 := (d2.setWidth 128) * 3916664325105025#128
  let v254 : BitVec 128 := v252 + u196
  let v255 : BitVec 128 := v254 + v253
  let v256 : BitVec 128 := v255 + u251
  v256

theorem carryGapSum2_bound (d1 d2 : BitVec 64) (u196 u251 : BitVec 128)
    (hd236 : d1.toNat < 2 ^ 52)
    (hd248 : d2.toNat < 2 ^ 52)
    (hu196 : u196.toNat < 2 ^ 110)
    (hu251 : u251.toNat < 2 ^ 110)
    : (carryGapSum2 d1 d2 u196 u251).toNat < 2 ^ 120 := by
  let v252 : BitVec 128 := (d1.setWidth 128) * 1367801#128
  obtain ⟨h252u, h252s, h252n⟩ := product_constant_flags d1 1367801#128 hd236 (by decide)
  let v253 : BitVec 128 := (d2.setWidth 128) * 3916664325105025#128
  obtain ⟨h253u, h253s, h253n⟩ := product_constant_flags d2 3916664325105025#128 hd248 (by decide)
  let v254 : BitVec 128 := v252 + u196
  have h254bound : (v252).toNat + (u196).toNat < 2 ^ 120 := by
    simp only [v252, v253, v254, h252n, h253n]
    norm_num at hd236 hd248 hu196 hu251 ⊢
    omega
  obtain ⟨h254u, h254s, h254n⟩ := product_add_flags (v252) (u196)
    (h254bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v252, v253, v254] at h254u h254s h254n
  let v255 : BitVec 128 := v254 + v253
  have h255bound : (v254).toNat + (v253).toNat < 2 ^ 120 := by
    simp only [v252, v253, v254, v255, h252n, h253n, h254n]
    norm_num at hd236 hd248 hu196 hu251 ⊢
    omega
  obtain ⟨h255u, h255s, h255n⟩ := product_add_flags (v254) (v253)
    (h255bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v252, v253, v254, v255] at h255u h255s h255n
  let v256 : BitVec 128 := v255 + u251
  have h256bound : (v255).toNat + (u251).toNat < 2 ^ 120 := by
    simp only [v252, v253, v254, v255, v256, h252n, h253n, h254n, h255n]
    norm_num at hd236 hd248 hu196 hu251 ⊢
    omega
  obtain ⟨h256u, h256s, h256n⟩ := product_add_flags (v255) (u251)
    (h256bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v252, v253, v254, v255, v256] at h256u h256s h256n
  change v256.toNat < 2 ^ 120
  rw [h256n]
  exact h256bound

def carryGapSum3 (d0 d2 d3 : BitVec 64) (u206 u263 : BitVec 128) : BitVec 128 :=
  let v264 : BitVec 128 := (d0.setWidth 128) <<< 44
  let v265 : BitVec 128 := (d2.setWidth 128) * 1367801#128
  let v266 : BitVec 128 := (d3.setWidth 128) * 3916664325105025#128
  let v267 : BitVec 128 := u206 + v264
  let v268 : BitVec 128 := v267 + v265
  let v269 : BitVec 128 := v268 + v266
  let v270 : BitVec 128 := v269 + u263
  v270

theorem carryGapSum3_bound (d0 d2 d3 : BitVec 64) (u206 u263 : BitVec 128)
    (hd226 : d0.toNat < 2 ^ 52)
    (hd248 : d2.toNat < 2 ^ 52)
    (hd260 : d3.toNat < 2 ^ 52)
    (hu206 : u206.toNat < 2 ^ 110)
    (hu263 : u263.toNat < 2 ^ 110)
    : (carryGapSum3 d0 d2 d3 u206 u263).toNat < 2 ^ 120 := by
  let v264 : BitVec 128 := (d0.setWidth 128) <<< 44
  obtain ⟨h264u, h264s, h264n⟩ := carry_shift44_flags d0 hd226
  let v265 : BitVec 128 := (d2.setWidth 128) * 1367801#128
  obtain ⟨h265u, h265s, h265n⟩ := product_constant_flags d2 1367801#128 hd248 (by decide)
  let v266 : BitVec 128 := (d3.setWidth 128) * 3916664325105025#128
  obtain ⟨h266u, h266s, h266n⟩ := product_constant_flags d3 3916664325105025#128 hd260 (by decide)
  let v267 : BitVec 128 := u206 + v264
  have h267bound : (u206).toNat + (v264).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, h264n, h265n, h266n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h267u, h267s, h267n⟩ := product_add_flags (u206) (v264)
    (h267bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267] at h267u h267s h267n
  let v268 : BitVec 128 := v267 + v265
  have h268bound : (v267).toNat + (v265).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, v268, h264n, h265n, h266n, h267n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h268u, h268s, h268n⟩ := product_add_flags (v267) (v265)
    (h268bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267, v268] at h268u h268s h268n
  let v269 : BitVec 128 := v268 + v266
  have h269bound : (v268).toNat + (v266).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, v268, v269, h264n, h265n, h266n, h267n, h268n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h269u, h269s, h269n⟩ := product_add_flags (v268) (v266)
    (h269bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267, v268, v269] at h269u h269s h269n
  let v270 : BitVec 128 := v269 + u263
  have h270bound : (v269).toNat + (u263).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, v268, v269, v270, h264n, h265n, h266n, h267n, h268n, h269n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h270u, h270s, h270n⟩ := product_add_flags (v269) (u263)
    (h270bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267, v268, v269, v270] at h270u h270s h270n
  change v270.toNat < 2 ^ 120
  rw [h270n]
  exact h270bound

def carryGapSum4 (d1 d3 d4 : BitVec 64) (u213 u277 : BitVec 128) : BitVec 128 :=
  let v278 : BitVec 128 := (d1.setWidth 128) <<< 44
  let v279 : BitVec 128 := (d3.setWidth 128) * 1367801#128
  let v280 : BitVec 128 := (d4.setWidth 128) * 3916664325105025#128
  let v281 : BitVec 128 := u213 + v278
  let v282 : BitVec 128 := v281 + v279
  let v283 : BitVec 128 := v282 + v280
  let v284 : BitVec 128 := v283 + u277
  let v285 : BitVec 64 := (v284).setWidth 64
  let v286 : BitVec 64 := v285 &&& 4503599627370495#64
  let v287 : BitVec 128 := v284 >>> 52
  v284

theorem carryGapSum4_bound (d1 d3 d4 : BitVec 64) (u213 u277 : BitVec 128)
    (hd236 : d1.toNat < 2 ^ 52)
    (hd260 : d3.toNat < 2 ^ 52)
    (hd274 : d4.toNat < 2 ^ 52)
    (hu213 : u213.toNat < 2 ^ 110)
    (hu277 : u277.toNat < 2 ^ 110)
    : (carryGapSum4 d1 d3 d4 u213 u277).toNat < 2 ^ 120 := by
  let v278 : BitVec 128 := (d1.setWidth 128) <<< 44
  obtain ⟨h278u, h278s, h278n⟩ := carry_shift44_flags d1 hd236
  let v279 : BitVec 128 := (d3.setWidth 128) * 1367801#128
  obtain ⟨h279u, h279s, h279n⟩ := product_constant_flags d3 1367801#128 hd260 (by decide)
  let v280 : BitVec 128 := (d4.setWidth 128) * 3916664325105025#128
  obtain ⟨h280u, h280s, h280n⟩ := product_constant_flags d4 3916664325105025#128 hd274 (by decide)
  let v281 : BitVec 128 := u213 + v278
  have h281bound : (u213).toNat + (v278).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, h278n, h279n, h280n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h281u, h281s, h281n⟩ := product_add_flags (u213) (v278)
    (h281bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281] at h281u h281s h281n
  let v282 : BitVec 128 := v281 + v279
  have h282bound : (v281).toNat + (v279).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, v282, h278n, h279n, h280n, h281n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h282u, h282s, h282n⟩ := product_add_flags (v281) (v279)
    (h282bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281, v282] at h282u h282s h282n
  let v283 : BitVec 128 := v282 + v280
  have h283bound : (v282).toNat + (v280).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, v282, v283, h278n, h279n, h280n, h281n, h282n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h283u, h283s, h283n⟩ := product_add_flags (v282) (v280)
    (h283bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281, v282, v283] at h283u h283s h283n
  let v284 : BitVec 128 := v283 + u277
  have h284bound : (v283).toNat + (u277).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, v282, v283, v284, h278n, h279n, h280n, h281n, h282n, h283n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h284u, h284s, h284n⟩ := product_add_flags (v283) (u277)
    (h284bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281, v282, v283, v284] at h284u h284s h284n
  let v285 : BitVec 64 := (v284).setWidth 64
  let v286 : BitVec 64 := v285 &&& 4503599627370495#64
  let v287 : BitVec 128 := v284 >>> 52
  change v284.toNat < 2 ^ 120
  rw [h284n]
  exact h284bound

def carryGapSum5 (d2 d4 : BitVec 64) (u218 u287 : BitVec 128) : BitVec 128 :=
  let v288 : BitVec 128 := (d2.setWidth 128) <<< 44
  let v289 : BitVec 128 := (d4.setWidth 128) * 1367801#128
  let v290 : BitVec 128 := v288 + u218
  let v291 : BitVec 128 := v290 + v289
  let v292 : BitVec 128 := v291 + u287
  let v293 : BitVec 64 := (v292).setWidth 64
  let v294 : BitVec 64 := v293 &&& 4503599627370495#64
  let v295 : BitVec 128 := v292 >>> 52
  v292

theorem carryGapSum5_bound (d2 d4 : BitVec 64) (u218 u287 : BitVec 128)
    (hd248 : d2.toNat < 2 ^ 52)
    (hd274 : d4.toNat < 2 ^ 52)
    (hu218 : u218.toNat < 2 ^ 110)
    (hu287 : u287.toNat < 2 ^ 110)
    : (carryGapSum5 d2 d4 u218 u287).toNat < 2 ^ 120 := by
  let v288 : BitVec 128 := (d2.setWidth 128) <<< 44
  obtain ⟨h288u, h288s, h288n⟩ := carry_shift44_flags d2 hd248
  let v289 : BitVec 128 := (d4.setWidth 128) * 1367801#128
  obtain ⟨h289u, h289s, h289n⟩ := product_constant_flags d4 1367801#128 hd274 (by decide)
  let v290 : BitVec 128 := v288 + u218
  have h290bound : (v288).toNat + (u218).toNat < 2 ^ 120 := by
    simp only [v288, v289, v290, h288n, h289n]
    norm_num at hd248 hd274 hu218 hu287 ⊢
    omega
  obtain ⟨h290u, h290s, h290n⟩ := product_add_flags (v288) (u218)
    (h290bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v288, v289, v290] at h290u h290s h290n
  let v291 : BitVec 128 := v290 + v289
  have h291bound : (v290).toNat + (v289).toNat < 2 ^ 120 := by
    simp only [v288, v289, v290, v291, h288n, h289n, h290n]
    norm_num at hd248 hd274 hu218 hu287 ⊢
    omega
  obtain ⟨h291u, h291s, h291n⟩ := product_add_flags (v290) (v289)
    (h291bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v288, v289, v290, v291] at h291u h291s h291n
  let v292 : BitVec 128 := v291 + u287
  have h292bound : (v291).toNat + (u287).toNat < 2 ^ 120 := by
    simp only [v288, v289, v290, v291, v292, h288n, h289n, h290n, h291n]
    norm_num at hd248 hd274 hu218 hu287 ⊢
    omega
  obtain ⟨h292u, h292s, h292n⟩ := product_add_flags (v291) (u287)
    (h292bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v288, v289, v290, v291, v292] at h292u h292s h292n
  let v293 : BitVec 64 := (v292).setWidth 64
  let v294 : BitVec 64 := v293 &&& 4503599627370495#64
  let v295 : BitVec 128 := v292 >>> 52
  change v292.toNat < 2 ^ 120
  rw [h292n]
  exact h292bound

def carryGapSum6 (d3 : BitVec 64) (u221 u295 : BitVec 128) : BitVec 128 :=
  let v296 : BitVec 128 := (d3.setWidth 128) <<< 44
  let v297 : BitVec 128 := v296 + u221
  let v298 : BitVec 128 := v297 + u295
  let v299 : BitVec 64 := (v298).setWidth 64
  let v300 : BitVec 64 := v299 &&& 4503599627370495#64
  let v301 : BitVec 128 := v298 >>> 52
  v298

theorem carryGapSum6_bound (d3 : BitVec 64) (u221 u295 : BitVec 128)
    (hd260 : d3.toNat < 2 ^ 52)
    (hu221 : u221.toNat < 2 ^ 110)
    (hu295 : u295.toNat < 2 ^ 110)
    : (carryGapSum6 d3 u221 u295).toNat < 2 ^ 120 := by
  let v296 : BitVec 128 := (d3.setWidth 128) <<< 44
  obtain ⟨h296u, h296s, h296n⟩ := carry_shift44_flags d3 hd260
  let v297 : BitVec 128 := v296 + u221
  have h297bound : (v296).toNat + (u221).toNat < 2 ^ 120 := by
    simp only [v296, v297, h296n]
    norm_num at hd260 hu221 hu295 ⊢
    omega
  obtain ⟨h297u, h297s, h297n⟩ := product_add_flags (v296) (u221)
    (h297bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v296, v297] at h297u h297s h297n
  let v298 : BitVec 128 := v297 + u295
  have h298bound : (v297).toNat + (u295).toNat < 2 ^ 120 := by
    simp only [v296, v297, v298, h296n, h297n]
    norm_num at hd260 hu221 hu295 ⊢
    omega
  obtain ⟨h298u, h298s, h298n⟩ := product_add_flags (v297) (u295)
    (h298bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v296, v297, v298] at h298u h298s h298n
  let v299 : BitVec 64 := (v298).setWidth 64
  let v300 : BitVec 64 := v299 &&& 4503599627370495#64
  let v301 : BitVec 128 := v298 >>> 52
  change v298.toNat < 2 ^ 120
  rw [h298n]
  exact h298bound

def carryGapSum7 (d4 : BitVec 64) (u222 u301 : BitVec 128) : BitVec 128 :=
  let v302 : BitVec 128 := (d4.setWidth 128) <<< 44
  let v303 : BitVec 128 := v302 + u222
  let v304 : BitVec 128 := v303 + u301
  let v305 : BitVec 64 := (v304).setWidth 64
  let v306 : BitVec 64 := v305 &&& 4503599627370495#64
  let v307 : BitVec 128 := v304 >>> 52
  let v308 : BitVec 64 := (v307).setWidth 64
  v304

theorem carryGapSum7_bound (d4 : BitVec 64) (u222 u301 : BitVec 128)
    (hd274 : d4.toNat < 2 ^ 52)
    (hu222 : u222.toNat < 2 ^ 110)
    (hu301 : u301.toNat < 2 ^ 110)
    : (carryGapSum7 d4 u222 u301).toNat < 2 ^ 120 := by
  let v302 : BitVec 128 := (d4.setWidth 128) <<< 44
  obtain ⟨h302u, h302s, h302n⟩ := carry_shift44_flags d4 hd274
  let v303 : BitVec 128 := v302 + u222
  have h303bound : (v302).toNat + (u222).toNat < 2 ^ 120 := by
    simp only [v302, v303, h302n]
    norm_num at hd274 hu222 hu301 ⊢
    omega
  obtain ⟨h303u, h303s, h303n⟩ := product_add_flags (v302) (u222)
    (h303bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v302, v303] at h303u h303s h303n
  let v304 : BitVec 128 := v303 + u301
  have h304bound : (v303).toNat + (u301).toNat < 2 ^ 120 := by
    simp only [v302, v303, v304, h302n, h303n]
    norm_num at hd274 hu222 hu301 ⊢
    omega
  obtain ⟨h304u, h304s, h304n⟩ := product_add_flags (v303) (u301)
    (h304bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v302, v303, v304] at h304u h304s h304n
  let v305 : BitVec 64 := (v304).setWidth 64
  let v306 : BitVec 64 := v305 &&& 4503599627370495#64
  let v307 : BitVec 128 := v304 >>> 52
  let v308 : BitVec 64 := (v307).setWidth 64
  have h308bound : (v307).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have h := h304bound
    rw [h304n]
    norm_num at h ⊢
    omega
  obtain ⟨h308u, h308s⟩ := carry_trunc64_flags (v307) h308bound
  dsimp only [v302, v303, v304, v305, v306, v307, v308] at h308u h308s
  change v304.toNat < 2 ^ 120
  rw [h304n]
  exact h304bound

end Agave.Ed25519.ScalarReduce32.Execution
