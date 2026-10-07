import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Maps
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline577Frame

/-! Exact instruction-list certificates in pieces of at most 25 instructions.
All overflow, disjointness, and GEP flags are retained by the register map. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
open LeanMLIR.RIR SerializerRename
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000

theorem take_map_append {α β : Type} (f : α → β) (s : List α) (t : List β)
    (start source n m : Nat)
    (hn : (t.drop start).take n = ((s.drop source).take n).map f)
    (hm : (t.drop (start + n)).take m = ((s.drop (source + n)).take m).map f) :
    (t.drop start).take (n + m) = ((s.drop source).take (n + m)).map f := by
  rw [List.take_add,List.take_add,List.map_append]
  simp only [List.drop_drop]
  rw [hn,hm]

theorem first_tail_chunk0 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 585).take 25 =
      (((ToBytes.program.entry).body.drop 54).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_chunk1 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 610).take 25 =
      (((ToBytes.program.entry).body.drop 79).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_chunk2 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 635).take 25 =
      (((ToBytes.program.entry).body.drop 104).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_chunk3 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 660).take 25 =
      (((ToBytes.program.entry).body.drop 129).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_chunk4 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 685).take 25 =
      (((ToBytes.program.entry).body.drop 154).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_chunk5 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 710).take 25 =
      (((ToBytes.program.entry).body.drop 179).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_chunk6 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 735).take 25 =
      (((ToBytes.program.entry).body.drop 204).take 25).map firstRenaming.instr := by
  rfl

theorem first_tail_names (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 585).take 175 =
      (((ToBytes.program.entry).body.drop 54).take 175).map firstRenaming.instr := by
  apply take_map_append firstRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 585 54 25 150 (first_tail_chunk0 p g)
  apply take_map_append firstRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 610 79 25 125 (first_tail_chunk1 p g)
  apply take_map_append firstRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 635 104 25 100 (first_tail_chunk2 p g)
  apply take_map_append firstRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 660 129 25 75 (first_tail_chunk3 p g)
  apply take_map_append firstRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 685 154 25 50 (first_tail_chunk4 p g)
  apply take_map_append firstRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 710 179 25 25 (first_tail_chunk5 p g)
  exact first_tail_chunk6 p g

theorem second_tail_chunk0 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 772).take 25 =
      (((ToBytes.program.entry).body.drop 54).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_chunk1 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 797).take 25 =
      (((ToBytes.program.entry).body.drop 79).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_chunk2 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 822).take 25 =
      (((ToBytes.program.entry).body.drop 104).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_chunk3 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 847).take 25 =
      (((ToBytes.program.entry).body.drop 129).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_chunk4 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 872).take 25 =
      (((ToBytes.program.entry).body.drop 154).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_chunk5 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 897).take 25 =
      (((ToBytes.program.entry).body.drop 179).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_chunk6 (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 922).take 25 =
      (((ToBytes.program.entry).body.drop 204).take 25).map secondRenaming.instr := by
  rfl

theorem second_tail_names (p : Primitives) (g : Globals) :
    ((program.entry p g).body.drop 772).take 175 =
      (((ToBytes.program.entry).body.drop 54).take 175).map secondRenaming.instr := by
  apply take_map_append secondRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 772 54 25 150 (second_tail_chunk0 p g)
  apply take_map_append secondRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 797 79 25 125 (second_tail_chunk1 p g)
  apply take_map_append secondRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 822 104 25 100 (second_tail_chunk2 p g)
  apply take_map_append secondRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 847 129 25 75 (second_tail_chunk3 p g)
  apply take_map_append secondRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 872 154 25 50 (second_tail_chunk4 p g)
  apply take_map_append secondRenaming.instr ToBytes.program.entry.body
    (program.entry p g).body 897 179 25 25 (second_tail_chunk5 p g)
  exact second_tail_chunk6 p g

theorem first_writes (p : Primitives) (g : Globals) :
    ∀ i ∈ ((program.entry p g).body.drop 577).take 183,
      SerializerFrame.writesAbove 431 i := by
  dsimp only [program.entry,List.drop,List.take]
  simp only [List.forall_mem_cons,SerializerFrame.writesAbove,true_and]
  repeat' apply And.intro
  all_goals first | decide | simp

theorem second_writes (p : Primitives) (g : Globals) :
    ∀ i ∈ ((program.entry p g).body.drop 760).take 187,
      SerializerFrame.writesAbove 579 i := by
  dsimp only [program.entry,List.drop,List.take]
  simp only [List.forall_mem_cons,SerializerFrame.writesAbove,true_and]
  repeat' apply And.intro
  all_goals first | decide | simp

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline577
