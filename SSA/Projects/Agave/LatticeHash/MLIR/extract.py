#!/usr/bin/env python3
"""Compile the pinned, verbatim Agave arch.rs plus exported observation wrappers.
Run on x86_64 with Rust 1.98.1 and LLVM/MLIR 22.1.8. No IR is synthesized.
The parent Batch/LtHash declarations are mirrored, not the complete Agave crate.
"""
import argparse, hashlib, json, pathlib, subprocess
p=argparse.ArgumentParser()
p.add_argument('--agave',type=pathlib.Path,required=True)
p.add_argument('--out',type=pathlib.Path,required=True)
p.add_argument('--rustc',default='rustc')
p.add_argument('--mlir-translate',default='mlir-translate')
a=p.parse_args(); a.out.mkdir(parents=True,exist_ok=True)
rel='lattice-hash/src/batch/arch.rs'
source=(a.agave/rel).read_bytes()
expected='6cef9f4897406efa5dfea7b3f16b799b0f71fb398cc017595351085ac4dc1ca0'
assert hashlib.sha256(source).hexdigest()==expected, 'Unexpected arch.rs source'
wrappers=[]
for width,ty,feature in [(8,'__m256i','avx2'),(16,'__m512i','avx512f,avx512bw')]:
 def wrap(name,args,body,ret=''):
  wrappers.append(f'\n#[unsafe(no_mangle)]\n#[target_feature(enable="{feature}")]\npub unsafe fn agave_{name}_{width}({args}) {ret} {{ unsafe {{ {body} }} }}\n')
 wrap('g',f'v: &mut [{ty}; 16], mx: {ty}, my: {ty}', 'g(v, 0, 4, 8, 12, mx, my);')
 wrap('compress_pre',f'cv: &[{ty}; 8], iv: &[{ty}; 8], m: &[{ty}; 16], lo: {ty}, hi: {ty}, len: {ty}, flags: {ty}', 'compress_pre(cv, iv, m, lo, hi, len, flags)',f'-> [{ty}; 16]')
 wrap('transpose',f'v: &mut [{ty}; {width}]',f'<{ty} as Lanes>::transpose(v);')
 wrap('add_u16',f'a: {ty}, b: {ty}','a.add_u16(b)',f'-> {ty}')
 wrap('batch',f'lanes: &[[u32; 256]; {width}], lengths: &[usize; {width}], acc: &mut LtHash',f'compress_batch::<{ty}>(Batch {{ lanes, lengths }}, acc);')
(a.out/'arch.rs').write_bytes(source+''.join(wrappers).encode())
(a.out/'harness.rs').write_text('''#![allow(private_interfaces)]
mod lt_hash { pub struct LtHash(pub [u16; 1024]); }
mod batch {
    const BLOCK_LEN: usize = 64;
    const MAX_LANES: usize = 16;
    type LaneBuf = [u32; 256];
    #[derive(Clone, Copy)]
    struct Batch<'a> { lanes: &'a [LaneBuf], lengths: &'a [usize] }
    impl Batch<'_> { fn len(&self) -> usize { self.lanes.len() } }
    #[path = "../arch.rs"]
    pub mod arch;
}
''')
# Rust resolves the path attribute relative to the inline module's directory.
(a.out/'batch').mkdir(exist_ok=True)
commands=[]
def run(cmd):
 commands.append(cmd); subprocess.run(cmd,check=True)
ll=a.out/'kernels.ll'; mlir=a.out/'kernels.mlir'
run([a.rustc,'--edition=2024','--crate-type=lib','--crate-name=agave_lthash_extract','--emit=llvm-ir','-C','opt-level=3','-C','panic=abort','-C','debug-assertions=no','-C','overflow-checks=no','-C','codegen-units=1','--target=x86_64-unknown-linux-gnu',str(a.out/'harness.rs'),'-o',str(ll)])
run([a.mlir_translate,'--import-llvm','--mlir-print-op-generic',str(ll),'-o',str(mlir)])
files={x.name:hashlib.sha256(x.read_bytes()).hexdigest() for x in [a.out/'arch.rs',a.out/'harness.rs',ll,mlir]}
manifest={'agave_commit':'e818d643945cd82c7144013af58ccf82d31df2dd','arch_sha256':expected,'source_prefix_bytes':len(source),'rustc':subprocess.check_output([a.rustc,'-vV'],text=True),'mlir_translate':subprocess.check_output([a.mlir_translate,'--version'],text=True),'commands':commands,'files_sha256':files,'boundary':'Verbatim pinned arch.rs compiled with appended wrappers and mirrored parent Batch/LtHash declarations; not a full Agave crate compilation or Rust/compiler correctness proof.'}
(a.out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(files,indent=2))
