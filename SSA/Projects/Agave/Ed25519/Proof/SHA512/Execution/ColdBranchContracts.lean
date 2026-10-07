import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Branches
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

/-- The short branch is discharged from a one-block primitive contract.
The compression input is observed after the actual length store, while its
chaining state is read before the branch's scratch writes. -/
theorem short_block_cold (g : CompressionGlobals) (p : Primitives)
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : OneBlockCompressContractUnder g p.sha512Compress compress)
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
    (htc : scratch.id ≠ chain.id)
    (hready : CompressionReady g s)
    (hcc : chain.id ≠ g.constants) (hcb : chain.id ≠ g.cache)
    (hbk : buffer.id ≠ g.constants) (hbb : buffer.id ≠ g.cache)
    (htc' : scratch.id ≠ g.constants) (htb : scratch.id ≠ g.cache) :
    ∃ after,
      (program p).runFrom E 2 s =
        (program p).runFrom (E[%167 := .value (buffer.add 112#64)]) 3 after ∧
      CacheFramedStoreEffect g (copyBlock (writeLength s buffer length) buffer scratch) after chain
        (compress.run (s.mem.readAt chain 512)
          (readBytes (writeLength s buffer length).mem buffer 128)) ∧
      after.WF ∧ CompressionReady g after := by
  let prepared := copyBlock (writeLength s buffer length) buffer scratch
  have hprepared : prepared.WF := hwf.storeAt.storeAt
  have hc' : SmallRange prepared.mem chain 64 := (hc.storeAt _ _).storeAt _ _
  have ht' : SmallRange prepared.mem scratch 128 := (ht.storeAt _ _).storeAt _ _
  have hpr : CompressionReady g prepared :=
    CompressionReady.storeAt g _ scratch _
      (CompressionReady.storeAt g s (buffer.add 112#64) length hready hbk hbb) htc' htb
  obtain ⟨after, hcall, he, hra⟩ := hcompress prepared chain scratch hprepared
    ⟨hpr, hcc, hcb, htb⟩ hc' ht'
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
    he.wellFormed hprepared, hra⟩
  simpa only [hread, hbytes] using he

/-- The two-call branch is discharged from the same one-block primitive
contract; no two-block or whole-digest correctness assumption is used. -/
theorem long_block_cold (g : CompressionGlobals) (p : Primitives)
    (compress : Agave.Ed25519.SHA512.Compression)
    (hcompress : OneBlockCompressContractUnder g p.sha512Compress compress)
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
    (hlc : last.id ≠ chain.id)
    (hready : CompressionReady g s)
    (hcc : chain.id ≠ g.constants) (hcb : chain.id ≠ g.cache)
    (hbk : buffer.id ≠ g.constants) (hbb : buffer.id ≠ g.cache)
    (hfk : first.id ≠ g.constants) (hfb' : first.id ≠ g.cache)
    (hlk : last.id ≠ g.constants) (hlb' : last.id ≠ g.cache) :
    ∃ middle after,
      (program p).runFrom E 1 s =
        (program p).runFrom (E[%166 := .value (buffer.add 112#64)]) 3 after ∧
      CacheFramedStoreEffect g (copyBlock s buffer first) middle chain
        (compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128)) ∧
      CacheFramedStoreEffect g
        (copyBlock (writeLength (clearPrefix middle buffer) buffer length) buffer last)
        after chain
        (compress.run
          (compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128))
          (readBytes (writeLength (clearPrefix middle buffer) buffer length).mem buffer 128)) ∧
      after.WF ∧ CompressionReady g middle ∧ CompressionReady g after := by
  let copied := copyBlock s buffer first
  have hcopied : copied.WF := hwf.storeAt
  have hcr : CompressionReady g copied := CompressionReady.storeAt g s first _ hready hfk hfb'
  obtain ⟨middle, hcallFirst, heFirst, hrMiddle⟩ := hcompress copied chain first hcopied
    ⟨hcr, hcc, hcb, hfb'⟩
    (hc.storeAt _ _) (hf.storeAt _ _) (Or.inl hfc.symm)
  have hreadFirst : copied.mem.readAt chain 512 = s.mem.readAt chain 512 :=
    readAt_storeAt_of_id_ne _ first chain _ _ hfc
  have hbytesFirst : readBytes copied.mem first 128 = readBytes s.mem buffer 128 :=
    readBytes_copy _ buffer first 128 hb hf
  have heFirst' : CacheFramedStoreEffect g copied middle chain
      (compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128)) := by
    simpa only [hreadFirst, hbytesFirst] using heFirst
  have hmiddle := heFirst.wellFormed hcopied
  have hbm : SmallRange middle.mem buffer 128 := (heFirst.cacheOutput hrMiddle hcb).smallRange buffer 128 hbb (hb.storeAt _ _)
  have hlm : SmallRange middle.mem last 128 := (heFirst.cacheOutput hrMiddle hcb).smallRange last 128 hlb' (hl.storeAt _ _)
  have hcm : SmallRange middle.mem chain 64 := (heFirst.cacheOutput hrMiddle hcb).smallRange chain 64 hcb (hc.storeAt _ _)
  have hchainMiddle : middle.mem.readAt chain 512 =
      compress.run (s.mem.readAt chain 512) (readBytes s.mem buffer 128) := by
    exact heFirst'.read_dst (hc.storeAt first (s.mem.readAt buffer 1024)).fits
  let prepared := copyBlock (writeLength (clearPrefix middle buffer) buffer length) buffer last
  have hprepared : prepared.WF := hmiddle.storeAt.storeAt.storeAt
  have hpr : CompressionReady g prepared :=
    CompressionReady.storeAt g _ last _
      (CompressionReady.storeAt g _ (buffer.add 112#64) length
        (CompressionReady.storeAt g middle buffer 0#896 hrMiddle hbk hbb) hbk hbb) hlk hlb'
  obtain ⟨after, hcallLast, heLast, hrAfter⟩ := hcompress prepared chain last hprepared
    ⟨hpr, hcc, hcb, hlb'⟩
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
    hcallFirst hcallLast, heFirst', ?_, heLast.wellFormed hprepared, hrMiddle, hrAfter⟩
  simpa only [hreadLast, hchainMiddle, hbytesLast] using heLast

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
