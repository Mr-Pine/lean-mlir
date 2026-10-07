import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Stores
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- Concrete contents of the registers read by the exact output slice. -/
structure StoreReady (E : Env program.Γ) (bytes : Bytes) : Prop where
  r47 : E.read (%47) = .value 1#64
  r48 : E.read (%48) = .value 2#64
  r49 : E.read (%49) = .value 3#64
  r1 : E.read (%1) = .value 4#64
  r3 : E.read (%3) = .value 5#64
  r5 : E.read (%5) = .value 6#64
  r7 : E.read (%7) = .value 7#64
  r9 : E.read (%9) = .value 8#64
  r50 : E.read (%50) = .value 9#64
  r51 : E.read (%51) = .value 10#64
  r52 : E.read (%52) = .value 11#64
  r10 : E.read (%10) = .value 12#64
  r11 : E.read (%11) = .value 13#64
  r12 : E.read (%12) = .value 14#64
  r53 : E.read (%53) = .value 15#64
  r13 : E.read (%13) = .value 16#64
  r54 : E.read (%54) = .value 17#64
  r14 : E.read (%14) = .value 18#64
  r15 : E.read (%15) = .value 19#64
  r17 : E.read (%17) = .value 20#64
  r55 : E.read (%55) = .value 21#64
  r56 : E.read (%56) = .value 22#64
  r57 : E.read (%57) = .value 23#64
  r16 : E.read (%16) = .value 24#64
  r18 : E.read (%18) = .value 25#64
  r19 : E.read (%19) = .value 26#64
  r58 : E.read (%58) = .value 27#64
  r45 : E.read (%45) = .value 28#64
  r59 : E.read (%59) = .value 29#64
  r20 : E.read (%20) = .value 30#64
  r60 : E.read (%60) = .value 31#64
  r351 : E.read (%351) = .value (bytes 0)
  r353 : E.read (%353) = .value (bytes 1)
  r355 : E.read (%355) = .value (bytes 2)
  r357 : E.read (%357) = .value (bytes 3)
  r359 : E.read (%359) = .value (bytes 4)
  r361 : E.read (%361) = .value (bytes 5)
  r365 : E.read (%365) = .value (bytes 6)
  r367 : E.read (%367) = .value (bytes 7)
  r369 : E.read (%369) = .value (bytes 8)
  r371 : E.read (%371) = .value (bytes 9)
  r373 : E.read (%373) = .value (bytes 10)
  r375 : E.read (%375) = .value (bytes 11)
  r377 : E.read (%377) = .value (bytes 12)
  r378 : E.read (%378) = .value (bytes 13)
  r380 : E.read (%380) = .value (bytes 14)
  r382 : E.read (%382) = .value (bytes 15)
  r384 : E.read (%384) = .value (bytes 16)
  r386 : E.read (%386) = .value (bytes 17)
  r388 : E.read (%388) = .value (bytes 18)
  r392 : E.read (%392) = .value (bytes 19)
  r394 : E.read (%394) = .value (bytes 20)
  r396 : E.read (%396) = .value (bytes 21)
  r398 : E.read (%398) = .value (bytes 22)
  r400 : E.read (%400) = .value (bytes 23)
  r402 : E.read (%402) = .value (bytes 24)
  r404 : E.read (%404) = .value (bytes 25)
  r405 : E.read (%405) = .value (bytes 26)
  r407 : E.read (%407) = .value (bytes 27)
  r409 : E.read (%409) = .value (bytes 28)
  r411 : E.read (%411) = .value (bytes 29)
  r413 : E.read (%413) = .value (bytes 30)
  r415 : E.read (%415) = .value (bytes 31)

/-- The store adapter's initialization is an identity at a ready environment. -/
theorem storeEnv_eq (E : Env program.Γ) (bytes : Bytes) (hr : StoreReady E bytes) :
    storeEnv E bytes = E := by
  unfold storeEnv
  rw [Env.write_of_read E (%47) hr.r47]
  rw [Env.write_of_read E (%48) hr.r48]
  rw [Env.write_of_read E (%49) hr.r49]
  rw [Env.write_of_read E (%1) hr.r1]
  rw [Env.write_of_read E (%3) hr.r3]
  rw [Env.write_of_read E (%5) hr.r5]
  rw [Env.write_of_read E (%7) hr.r7]
  rw [Env.write_of_read E (%9) hr.r9]
  rw [Env.write_of_read E (%50) hr.r50]
  rw [Env.write_of_read E (%51) hr.r51]
  rw [Env.write_of_read E (%52) hr.r52]
  rw [Env.write_of_read E (%10) hr.r10]
  rw [Env.write_of_read E (%11) hr.r11]
  rw [Env.write_of_read E (%12) hr.r12]
  rw [Env.write_of_read E (%53) hr.r53]
  rw [Env.write_of_read E (%13) hr.r13]
  rw [Env.write_of_read E (%54) hr.r54]
  rw [Env.write_of_read E (%14) hr.r14]
  rw [Env.write_of_read E (%15) hr.r15]
  rw [Env.write_of_read E (%17) hr.r17]
  rw [Env.write_of_read E (%55) hr.r55]
  rw [Env.write_of_read E (%56) hr.r56]
  rw [Env.write_of_read E (%57) hr.r57]
  rw [Env.write_of_read E (%16) hr.r16]
  rw [Env.write_of_read E (%18) hr.r18]
  rw [Env.write_of_read E (%19) hr.r19]
  rw [Env.write_of_read E (%58) hr.r58]
  rw [Env.write_of_read E (%45) hr.r45]
  rw [Env.write_of_read E (%59) hr.r59]
  rw [Env.write_of_read E (%20) hr.r20]
  rw [Env.write_of_read E (%60) hr.r60]
  rw [Env.write_of_read E (%351) hr.r351]
  rw [Env.write_of_read E (%353) hr.r353]
  rw [Env.write_of_read E (%355) hr.r355]
  rw [Env.write_of_read E (%357) hr.r357]
  rw [Env.write_of_read E (%359) hr.r359]
  rw [Env.write_of_read E (%361) hr.r361]
  rw [Env.write_of_read E (%365) hr.r365]
  rw [Env.write_of_read E (%367) hr.r367]
  rw [Env.write_of_read E (%369) hr.r369]
  rw [Env.write_of_read E (%371) hr.r371]
  rw [Env.write_of_read E (%373) hr.r373]
  rw [Env.write_of_read E (%375) hr.r375]
  rw [Env.write_of_read E (%377) hr.r377]
  rw [Env.write_of_read E (%378) hr.r378]
  rw [Env.write_of_read E (%380) hr.r380]
  rw [Env.write_of_read E (%382) hr.r382]
  rw [Env.write_of_read E (%384) hr.r384]
  rw [Env.write_of_read E (%386) hr.r386]
  rw [Env.write_of_read E (%388) hr.r388]
  rw [Env.write_of_read E (%392) hr.r392]
  rw [Env.write_of_read E (%394) hr.r394]
  rw [Env.write_of_read E (%396) hr.r396]
  rw [Env.write_of_read E (%398) hr.r398]
  rw [Env.write_of_read E (%400) hr.r400]
  rw [Env.write_of_read E (%402) hr.r402]
  rw [Env.write_of_read E (%404) hr.r404]
  rw [Env.write_of_read E (%405) hr.r405]
  rw [Env.write_of_read E (%407) hr.r407]
  rw [Env.write_of_read E (%409) hr.r409]
  rw [Env.write_of_read E (%411) hr.r411]
  rw [Env.write_of_read E (%413) hr.r413]
  rw [Env.write_of_read E (%415) hr.r415]

/-- The actual caller's environment suffices; no synthetic register replacement
is made once the packing and constant-register facts have been established. -/
theorem store_phase (E : Env program.Γ) (s : GlobalState) (out : Pointer) (bytes : Bytes)
    (hfit : SmallRange s.mem out 32) (hout : E.read (%arg0) = .value out)
    (hr : StoreReady E bytes) :
    List.foldlM Instr.run E stores s =
      .value (storeFinalEnv E out, {s with mem := storeBytes s.mem out bytes}) := by
  have h := store_body E out bytes s hfit hout
  rw [storeEnv_eq E bytes hr] at h
  exact h

end Agave.Ed25519.ScalarReduce32.Execution
