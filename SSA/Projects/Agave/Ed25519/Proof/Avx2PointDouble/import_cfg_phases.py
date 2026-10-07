#!/usr/bin/env python3
"""Untrusted bb18 slice-source generator; Lean checks execution equalities against the exact imported CFG."""
from pathlib import Path
import argparse,importlib.util,re
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true',help='verify the generated Lean source without writing it')
args=parser.parse_args()
root=Path(__file__).resolve().parent.parent
spec=importlib.util.spec_from_file_location('gen',root/'Avx2PointAdd/import_cfg_phases.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
blocks,digest=m.source_blocks(); b=blocks[18]
head='''import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.MixingPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame
import SSA.Projects.RIR.Run.Memory

/-! Exact instruction intervals of the unchanged imported bb18. These source
proofs expose every write and keep helper bodies behind their proved local
contracts. The C/LLVM extraction and this generator are not trusted axioms. -/
namespace Agave.Ed25519.Avx2PointDouble.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
open Avx2PointAdd.Phases (packed_unflatten)
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

structure Constants (E : ⟪avx2Kernel.Γ⟫) : Prop where
  poison : E.read (%26) = Ty.poisoned (.vec 8 32)
  one : E.read (%27) = Ty.wrap (#v[1, 1, 1, 1, 1, 1, 1, 1] : Vec32)
  «prefix» : E.read (%45) = zeroPrefix
  difference : E.read (%62) = zeroDifference
  lazy0 : E.read (%81) = lazyConstants 134217690#32 67108862#32
  lazyN : E.read (%99) = lazyConstants 134217726#32 67108862#32
  sum : E.read (%116) = zeroSum

structure Pointers (E : ⟪avx2Kernel.Γ⟫) (prepared square result : Pointer) : Prop where
'''
for ptr,regs in [('prepared',[256,327,328,329,330]),('square',[255,331,332,333,334]),('result',[263,335,336,337,338])]:
 for k,r in enumerate(regs): head+=f'  r{r} : E.read (%{r}) = .value ({ptr}'+(f'.add {k*32}#64' if k else '')+')\n'
head+='\ndef inputReads (E : ⟪avx2Kernel.Γ⟫) (a : Blocks) : Prop :=\n  '+' ∧\n  '.join(f'E.read (%{r}) = Ty.wrap (a {k})' for k,r in enumerate([424,423,422,421,425]))+'\n\n'

def raw_env(name,start,end,loadmap={}):
 entries=[];known={};lets=[]
 for line in b[start:end]:
  if '"llvm.intr.lifetime.' in line: continue
  match=re.fullmatch(r'%(\d+) = "llvm\.(shufflevector|sub|add|shl|load)"\(([^)]*)\)(.*?) : \(.*',line)
  assert match,line
  dst,op,args,attrs=match.groups();args=re.findall(r'%(\d+)',args)
  if op=='load': expr=f'Ty.wrap (v {loadmap[int(dst)]})'
  else:
   aa=[known.get(r,f'(E.read (%{r}))') for r in args]
   if op=='shufflevector':
    mask=map(int,re.search(r'mask = array<i32: ([^>]+)>',attrs)[1].split(','))
    expr='Operation.shufflevector #v['+', '.join('none' if k<0 else f'some {k}' for k in mask)+f'] {aa[0]} {aa[1]}'
   else: expr=f'Vector.zipWith (Operation.{op} {{}}) {aa[0]} {aa[1]}'
  entries.append(dst);lets.append(f'  let v{dst} : ⟦Ty.vec 8 32⟧ := {expr}');known[dst]='v'+dst
 text=f'def {name}Env (E : ⟪avx2Kernel.Γ⟫)'+(' (v : Blocks)' if loadmap else '')+' : ⟪avx2Kernel.Γ⟫ :=\n'+'\n'.join(lets)+'\n  E['+',\n    '.join(f'%{d} := v{d}' for d in entries)+']\n\n'
 text+=f'theorem {name}_frame (E : ⟪avx2Kernel.Γ⟫)'+(' (v : Blocks)' if loadmap else '')+f' :\n    RegisterFrame 427 avx2Kernel.Γ.n E ({name}Env E'+(' v' if loadmap else '')+') := by\n'
 text+=f'  unfold {name}Env\n  repeat\' apply RegisterFrame.write (hd := by decide)\n  exact RegisterFrame.refl _ _ _\n\n'
 return text
head+=raw_env('prepare',0,23)
head+='''theorem prepare_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb18 p) E 0 23 s = .value (prepareEnv E, s) := by
  simp [runSlice, avx2Kernel.bb18, prepareEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env]

def preparedReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%442), E.read (%443), E.read (%444), E.read (%445), E.read (%446)]

theorem prepare_field (E : ⟪avx2Kernel.Γ⟫) (a : Blocks)
    (hc : Constants E) (ha : inputReads E a) (k : Fin 5) :
    preparedReads (prepareEnv E) k = Ty.wrap (prepareBlocks a k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  have hnetwork : preparedReads (prepareEnv E) k = prepareOperation (Ty.wrap (a k)) := by
    fin_cases k <;> simp [preparedReads, prepareEnv, prepareOperation, maskA, maskB,
      maskBlend, hc.poison, h0, h1, h2, h3, h4, mlir_env]
  exact hnetwork.trans (prepareOperation_value (a k))

'''
head+=raw_env('mix',29,94,{447:0,448:1,449:2,450:3,455:4})
head+='''theorem mix_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks)
    (hr : SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%255) = .value r)
    (hp1 : E.read (%331) = .value (r.add 32#64))
    (hp2 : E.read (%332) = .value (r.add 64#64))
    (hp3 : E.read (%333) = .value (r.add 96#64))
    (hp4 : E.read (%334) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb18 p) E 29 65 s = .value (mixEnv E v, s) := by
'''
for k in range(5):
 head+=f'  have hf{k} := hr.fits_add (k := {32*k}) (count := 32) (by decide)\n  have hv{k} := packed_unflatten s.mem r v hv {k}\n  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add {32*k}#64) 256) = Ty.wrap (v {k}) at hv{k}\n  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv{k}\n'
head+='''  simp only [Pointer.add_zero] at hf0 hv0
  simp (config := {maxSteps := 500000}) [runSlice, avx2Kernel.bb18, mixEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.load, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hf0, hv0, hp1, hf1, hv1,
    hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4, -reduceShufflevector]

def mixedReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%494), E.read (%497), E.read (%500), E.read (%503), E.read (%506)]
def rightReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%507), E.read (%508), E.read (%509), E.read (%510), E.read (%511)]

theorem mix_network (E : ⟪avx2Kernel.Γ⟫) (v : Blocks)
    (hc : Constants E) (k : Fin 5) :
    mixedReads (mixEnv E v) k = mixOperation (Ty.wrap (v k))
      (Avx2PointAdd.Phases.evenConstant k) (Avx2PointAdd.Phases.oddConstant k) := by
  fin_cases k <;> simp [mixedReads, mixEnv, mixOperation, hc.poison, hc.one,
    hc.prefix, hc.difference, hc.lazy0, hc.lazyN, hc.sum,
    Avx2PointAdd.Phases.evenConstant, Avx2PointAdd.Phases.oddConstant,
    Avx2PointAdd.Phases.evenIndex, Avx2PointAdd.Phases.oddIndex,
    Avx2PointAdd.twiceP, Avx2PointAdd.word, mlir_env]

theorem mix_field (E : ⟪avx2Kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    mixedReads (mixEnv E (packCoordinates q)) k = Ty.wrap (packCoordinates (mix q) k) := by
  rw [mix_network E _ hc k, mixOperation_value, mixBlock_packed hq]

theorem right_field (E : ⟪avx2Kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    rightReads (mixEnv E (packCoordinates q)) k = Ty.wrap (packCoordinates (right q) k) := by
  have h : rightReads (mixEnv E (packCoordinates q)) k =
      Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7]
        (mixedReads (mixEnv E (packCoordinates q)) k) (Ty.poisoned (.vec 8 32)) := by
    fin_cases k <;> simp [rightReads, mixedReads, mixEnv, hc.poison, mlir_env]
  rw [h, mix_field E q hc hq k, rightBlock_shuffle, rightBlock_packed]

'''
head+=raw_env('left',99,104)
head+='''theorem left_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    runSlice (avx2Kernel.bb18 p) E 99 5 s = .value (leftEnv E, s) := by
  simp [runSlice, avx2Kernel.bb18, leftEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env]

def leftReads (E : ⟪avx2Kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%512), E.read (%513), E.read (%514), E.read (%515), E.read (%516)]

theorem left_field (E : ⟪avx2Kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    leftReads (leftEnv (mixEnv E (packCoordinates q))) k = Ty.wrap (packCoordinates (left q) k) := by
  have h : leftReads (leftEnv (mixEnv E (packCoordinates q))) k =
      Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2]
        (mixedReads (mixEnv E (packCoordinates q)) k) (Ty.poisoned (.vec 8 32)) := by
    fin_cases k <;> simp [leftReads, leftEnv, mixedReads, mixEnv, hc.poison, mlir_env]
  rw [h, mix_field E q hc hq k, leftBlock_shuffle, leftBlock_packed]

'''
# One exact local store rule for each of the three five-vector store phases.
for name,start,prs,vrs in [('prepared',23,[256,327,328,329,330],range(442,447)),('right',94,[255,331,332,333,334],range(507,512)),('left',104,[256,327,328,329,330],range(512,517))]:
 head+=f'theorem {name}_stores (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)\n    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)\n'
 for k,(pr,vr) in enumerate(zip(prs,vrs)):
  pexpr='r' if k==0 else f'(r.add {k*32}#64)'
  head+=f'    (hp{k} : E.read (%{pr}) = .value {pexpr})\n    (hv{k} : E.read (%{vr}) = Ty.wrap (v {k}))'+(' :\n' if k==4 else '\n')
 head+=f'    runSlice (avx2Kernel.bb18 p) E {start} 5 s =\n      .value (E, {{s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}}) := by\n'
 for k in range(5): head+=f'  have hf{k} := hr.fits_add (k := {32*k}) (count := 32) (by decide)\n'
 head+='  simp only [Pointer.add_zero] at hf0\n'
 head+='  simp [runSlice, avx2Kernel.bb18, Avx2FieldMul.Execution.storeBlocks,\n    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,\n    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,\n    mlir_effect, mlir_env, throwUBIf, '+', '.join(f'hp{k}, hv{k}, hf{k}' for k in range(5))+']\n\n'
# Final loads with lifetime hints.
head+=raw_env('loadResult',110,118,{517:0,518:1,519:2,520:3,521:4})
head+='''theorem loadResult_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%263) = .value r)
    (hp1 : E.read (%335) = .value (r.add 32#64))
    (hp2 : E.read (%336) = .value (r.add 64#64))
    (hp3 : E.read (%337) = .value (r.add 96#64))
    (hp4 : E.read (%338) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb18 p) E 110 8 s = .value (loadResultEnv E v, s) := by
'''
for k in range(5): head+=f'  have hf{k} := hr.fits_add (k := {32*k}) (count := 32) (by decide)\n  have hv{k} := packed_unflatten s.mem r v hv {k}\n  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add {32*k}#64) 256) = Ty.wrap (v {k}) at hv{k}\n  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv{k}\n'
head+='''  simp only [Pointer.add_zero] at hf0 hv0
  simp [runSlice, avx2Kernel.bb18, loadResultEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Operation.load, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hf0, hv0, hp1, hf1, hv1,
    hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

end Agave.Ed25519.Avx2PointDouble.CFG
'''
target=root/'Avx2PointDouble/CFGPhases.lean'
if args.check:
 if target.read_text()!=head: parser.error(f'generated source differs: {target}')
else:
 target.write_text(head)
print('checked' if args.check else 'wrote',len(head.splitlines()),'lines; source region sha256',digest)
