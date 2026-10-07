import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Branches
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

/-- The short branch is discharged from a one-block primitive contract.
The compression input is observed after the actual length store, while its
chaining state is read before the branch's scratch writes. -/
theorem short_block_of_contract (p : Primitives)
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : OneBlockCompressContract p.sha512Compress compress)
    (E : Env program.Γ) (s : GlobalState) (buffer scratch chain : Pointer)
    (length : BitVec 128)
    (hbuffer : E.read (%84) = .value buffer)
    (hscratch : E.read (%81) = .value scratch)
    (hchain : E.read (%151) = .value chain)
    (hlength : E.read (%161) = .value length)
    (h112 : E.read (%10) = .value 112#64)
    (h128 : E.read (%2) = .value 128#64)
    (h1 : E.read (%12) = .value 1#64)
    (hwf : s.WF) (hb : SmallRange s.mem buffer 128)
    (ht : SmallRange s.mem scratch 128) (hc : SmallRange s.mem chain 64)
    (hne : scratch.id ≠ buffer.id) (hbc : buffer.id ≠ chain.id)
    (htc : scratch.id ≠ chain.id) :
    ∃ after,
      (program p).runFrom E 2 s =
        (program p).runFrom (E[%167 := .value (buffer.add 112#64)]) 3 after ∧
      StoreEffect (copyBlock (writeLength s buffer length) buffer scratch) after chain
        (compress.run (s.mem.readAt chain 512)
          (readBytes (writeLength s buffer length).mem buffer 128)) ∧
      after.WF := by
  let prepared := copyBlock (writeLength s buffer length) buffer scratch
  have hprepared : prepared.WF := hwf.storeAt.storeAt
  have hc' : SmallRange prepared.mem chain 64 := (hc.storeAt _ _).storeAt _ _
  have ht' : SmallRange prepared.mem scratch 128 := (ht.storeAt _ _).storeAt _ _
  obtain ⟨after, hcall, he⟩ := hcompress prepared chain scratch hprepared hc' ht'
    (Or.inl htc.symm)
  have hread : prepared.mem.readAt chain 512 = s.mem.readAt chain 512 := by
    dsimp [prepared, copyBlock, writeLength]
    rw [readAt_storeAt_of_id_ne _ scratch chain _ _ htc,
      readAt_storeAt_of_id_ne _ (buffer.add 112#64) chain _ _ hbc]
  have hbytes : readBytes prepared.mem scratch 128 =
      readBytes (writeLength s buffer length).mem buffer 128 :=
    readBytes_copy _ buffer scratch 128 (hb.storeAt _ _) (ht.storeAt _ _)
  refine ⟨after, short_block p E s after buffer scratch chain length
    hbuffer hscratch hchain hlength h112 h128 h1 hb ht hne hcall, ?_,
    he.wellFormed hprepared⟩
  simpa only [hread, hbytes] using he

/-- The two-call branch is discharged from the same one-block primitive
contract; no two-block or whole-digest correctness assumption is used. -/
theorem long_block_of_contract (p : Primitives)
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : OneBlockCompressContract p.sha512Compress compress)
    (E : Env program.Γ) (s : GlobalState) (buffer first last chain : Pointer)
    (length : BitVec 128)
    (hbuffer : E.read (%84) = .value buffer)
    (hfirst : E.read (%83) = .value first)
    (hlast : E.read (%82) = .value last)
    (hchain : E.read (%151) = .value chain)
    (hlength : E.read (%161) = .value length)
    (h112 : E.read (%10) = .value 112#64)
    (h128 : E.read (%2) = .value 128#64)
    (h1 : E.read (%12) = .value 1#64)
    (h0 : E.read (%8) = .value 0#8)
    (hwf : s.WF) (hb : SmallRange s.mem buffer 128)
    (hf : SmallRange s.mem first 128) (hl : SmallRange s.mem last 128)
    (hc : SmallRange s.mem chain 64)
    (hfb : first.id ≠ buffer.id) (hlb : last.id ≠ buffer.id)
    (hbc : buffer.id ≠ chain.id) (hfc : first.id ≠ chain.id)
    (hlc : last.id ≠ chain.id) :
    ∃ middle after,
      (program p).runFrom E 1 s =
        (program p).runFrom (E[%166 := .value (buffer.add 112#64)]) 3 after ∧
      StoreEffect (copyBlock s buffer first) middle chain
        (compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128)) ∧
      StoreEffect
        (copyBlock (writeLength (clearPrefix middle buffer) buffer length) buffer last)
        after chain
        (compress.run
          (compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128))
          (readBytes (writeLength (clearPrefix middle buffer) buffer length).mem buffer 128)) ∧
      after.WF := by
  let copied := copyBlock s buffer first
  have hcopied : copied.WF := hwf.storeAt
  obtain ⟨middle, hcallFirst, heFirst⟩ := hcompress copied chain first hcopied
    (hc.storeAt _ _) (hf.storeAt _ _) (Or.inl hfc.symm)
  have hreadFirst : copied.mem.readAt chain 512 = s.mem.readAt chain 512 :=
    readAt_storeAt_of_id_ne _ first chain _ _ hfc
  have hbytesFirst : readBytes copied.mem first 128 = readBytes s.mem buffer 128 :=
    readBytes_copy _ buffer first 128 hb hf
  have heFirst' : StoreEffect copied middle chain
      (compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128)) := by
    simpa only [hreadFirst, hbytesFirst] using heFirst
  have hmiddle := heFirst.wellFormed hcopied
  have hbm : SmallRange middle.mem buffer 128 := heFirst.smallRange (hb.storeAt _ _)
  have hlm : SmallRange middle.mem last 128 := heFirst.smallRange (hl.storeAt _ _)
  have hcm : SmallRange middle.mem chain 64 := heFirst.smallRange (hc.storeAt _ _)
  have hchainMiddle : middle.mem.readAt chain 512 =
      compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128) := by
    rw [heFirst'.memory]
    exact MemoryState.readAt_storeAt_self
      (hc.storeAt first (s.mem.readAt buffer 1024)).fits _
  let prepared := copyBlock (writeLength (clearPrefix middle buffer) buffer length) buffer last
  have hprepared : prepared.WF := hmiddle.storeAt.storeAt.storeAt
  obtain ⟨after, hcallLast, heLast⟩ := hcompress prepared chain last hprepared
    (((hcm.storeAt _ _).storeAt _ _).storeAt _ _)
    (((hlm.storeAt _ _).storeAt _ _).storeAt _ _) (Or.inl hlc.symm)
  have hreadLast : prepared.mem.readAt chain 512 = middle.mem.readAt chain 512 := by
    dsimp [prepared, copyBlock, writeLength, clearPrefix]
    rw [readAt_storeAt_of_id_ne _ last chain _ _ hlc,
      readAt_storeAt_of_id_ne _ (buffer.add 112#64) chain _ _ hbc,
      readAt_storeAt_of_id_ne _ buffer chain _ _ hbc]
  have hbytesLast : readBytes prepared.mem last 128 =
      readBytes (writeLength (clearPrefix middle buffer) buffer length).mem buffer 128 :=
    readBytes_copy _ buffer last 128 ((hbm.storeAt _ _).storeAt _ _)
      ((hlm.storeAt _ _).storeAt _ _)
  refine ⟨middle, after, long_block p E s middle after buffer first last chain length
    hbuffer hfirst hlast hchain hlength h112 h128 h1 h0 hb hf hbm hlm hfb hlb
    hcallFirst hcallLast, heFirst', ?_, heLast.wellFormed hprepared⟩
  simpa only [hreadLast, hchainMiddle, hbytesLast] using heLast

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
