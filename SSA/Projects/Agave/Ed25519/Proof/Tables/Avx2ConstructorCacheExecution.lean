import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCachePhases

/-! Compose the checked pure intervals inside the original constructor body.
These equalities preserve the exact remaining instructions after each phase. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CachePhases
open LeanMLIR.RIR
open Avx2PointAdd.CFG (runBodyFrom_slice)
set_option maxRecDepth 10000

def normalizeResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  normalize1 (normalize0 (E))

theorem normalize_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb0 p).runBodyFrom E 480 s =
      (kernel.bb0 p).runBodyFrom (normalizeResult E) 505 s := by
  let E1 := normalize0 E
  let E2 := normalize1 E1
  calc
    (kernel.bb0 p).runBodyFrom E 480 s = (kernel.bb0 p).runBodyFrom E1 495 s :=
      runBodyFrom_slice _ E E1 480 15 s s (normalize0_slice p E s)
    _ = (kernel.bb0 p).runBodyFrom E2 505 s :=
      runBodyFrom_slice _ E1 E2 495 10 s s (normalize1_slice p E1 s)

def initialCacheResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  initialCache9 (initialCache8 (initialCache7 (initialCache6 (initialCache5 (initialCache4 (initialCache3 (initialCache2 (initialCache1 (initialCache0 (E))))))))))

theorem initialCache_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb0 p).runBodyFrom E 505 s =
      (kernel.bb0 p).runBodyFrom (initialCacheResult E) 650 s := by
  let E1 := initialCache0 E
  let E2 := initialCache1 E1
  let E3 := initialCache2 E2
  let E4 := initialCache3 E3
  let E5 := initialCache4 E4
  let E6 := initialCache5 E5
  let E7 := initialCache6 E6
  let E8 := initialCache7 E7
  let E9 := initialCache8 E8
  let E10 := initialCache9 E9
  calc
    (kernel.bb0 p).runBodyFrom E 505 s = (kernel.bb0 p).runBodyFrom E1 520 s :=
      runBodyFrom_slice _ E E1 505 15 s s (initialCache0_slice p E s)
    _ = (kernel.bb0 p).runBodyFrom E2 535 s :=
      runBodyFrom_slice _ E1 E2 520 15 s s (initialCache1_slice p E1 s)
    _ = (kernel.bb0 p).runBodyFrom E3 550 s :=
      runBodyFrom_slice _ E2 E3 535 15 s s (initialCache2_slice p E2 s)
    _ = (kernel.bb0 p).runBodyFrom E4 565 s :=
      runBodyFrom_slice _ E3 E4 550 15 s s (initialCache3_slice p E3 s)
    _ = (kernel.bb0 p).runBodyFrom E5 580 s :=
      runBodyFrom_slice _ E4 E5 565 15 s s (initialCache4_slice p E4 s)
    _ = (kernel.bb0 p).runBodyFrom E6 595 s :=
      runBodyFrom_slice _ E5 E6 580 15 s s (initialCache5_slice p E5 s)
    _ = (kernel.bb0 p).runBodyFrom E7 610 s :=
      runBodyFrom_slice _ E6 E7 595 15 s s (initialCache6_slice p E6 s)
    _ = (kernel.bb0 p).runBodyFrom E8 625 s :=
      runBodyFrom_slice _ E7 E8 610 15 s s (initialCache7_slice p E7 s)
    _ = (kernel.bb0 p).runBodyFrom E9 640 s :=
      runBodyFrom_slice _ E8 E9 625 15 s s (initialCache8_slice p E8 s)
    _ = (kernel.bb0 p).runBodyFrom E10 650 s :=
      runBodyFrom_slice _ E9 E10 640 10 s s (initialCache9_slice p E9 s)

def successorCacheResult (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  successorCache9 (successorCache8 (successorCache7 (successorCache6 (successorCache5 (successorCache4 (successorCache3 (successorCache2 (successorCache1 (successorCache0 (E))))))))))

theorem successorCache_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 105 s =
      (kernel.bb2 p).runBodyFrom (successorCacheResult E) 250 s := by
  let E1 := successorCache0 E
  let E2 := successorCache1 E1
  let E3 := successorCache2 E2
  let E4 := successorCache3 E3
  let E5 := successorCache4 E4
  let E6 := successorCache5 E5
  let E7 := successorCache6 E6
  let E8 := successorCache7 E7
  let E9 := successorCache8 E8
  let E10 := successorCache9 E9
  calc
    (kernel.bb2 p).runBodyFrom E 105 s = (kernel.bb2 p).runBodyFrom E1 120 s :=
      runBodyFrom_slice _ E E1 105 15 s s (successorCache0_slice p E s)
    _ = (kernel.bb2 p).runBodyFrom E2 135 s :=
      runBodyFrom_slice _ E1 E2 120 15 s s (successorCache1_slice p E1 s)
    _ = (kernel.bb2 p).runBodyFrom E3 150 s :=
      runBodyFrom_slice _ E2 E3 135 15 s s (successorCache2_slice p E2 s)
    _ = (kernel.bb2 p).runBodyFrom E4 165 s :=
      runBodyFrom_slice _ E3 E4 150 15 s s (successorCache3_slice p E3 s)
    _ = (kernel.bb2 p).runBodyFrom E5 180 s :=
      runBodyFrom_slice _ E4 E5 165 15 s s (successorCache4_slice p E4 s)
    _ = (kernel.bb2 p).runBodyFrom E6 195 s :=
      runBodyFrom_slice _ E5 E6 180 15 s s (successorCache5_slice p E5 s)
    _ = (kernel.bb2 p).runBodyFrom E7 210 s :=
      runBodyFrom_slice _ E6 E7 195 15 s s (successorCache6_slice p E6 s)
    _ = (kernel.bb2 p).runBodyFrom E8 225 s :=
      runBodyFrom_slice _ E7 E8 210 15 s s (successorCache7_slice p E7 s)
    _ = (kernel.bb2 p).runBodyFrom E9 240 s :=
      runBodyFrom_slice _ E8 E9 225 15 s s (successorCache8_slice p E8 s)
    _ = (kernel.bb2 p).runBodyFrom E10 250 s :=
      runBodyFrom_slice _ E9 E10 240 10 s s (successorCache9_slice p E9 s)

end Agave.Ed25519.Tables.Avx2Constructor.CachePhases
