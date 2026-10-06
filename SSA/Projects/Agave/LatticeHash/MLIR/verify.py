#!/usr/bin/env python3
"""Read-only artifact provenance verification; no compiler or Lean required.
The reviewed provenance.lock.json is the trust anchor, not a cryptographic
signature. A coordinated malicious edit to it and all artifacts requires review.
"""
import argparse, hashlib, json, pathlib, re, shutil, subprocess, sys, tempfile
ROOT = pathlib.Path(__file__).resolve().parent
AGAVE = 'e818d643945cd82c7144013af58ccf82d31df2dd'
ARCH = '6cef9f4897406efa5dfea7b3f16b799b0f71fb398cc017595351085ac4dc1ca0'
AGAVE_FILES = {
    'lattice-hash/src/batch/arch.rs': ARCH,
    'lattice-hash/src/batch.rs': 'fdccfacf2d2475f129a9326188d688b4db0cc2a8f156cf65c87cde44becd1394',
    'lattice-hash/src/lt_hash.rs': '2a2723d0ea4d6130b22ae76a6a5b677e95eabe4dd7062d756c137fd9d22d6a7a',
    'Cargo.lock': '1230c33b5344dc38474a99c388e0343869e4e174485f544818db8303e0205990',
}
BLAKE = {'portable.rs':'85ed8cd8f601e6801c0a26358c7ac70e29759445cfe39c584f40af072a201601','lib.rs':'a187904c4b12ea7c100557c0f167cc91a034e391ddeb56c9db65f7d400a4b566','platform.rs':'954e3564bb976c333cfaa68fc672a8543afc2e021c8b89e8d9393816b0ad90d1'}
BASE_SYMBOLS = {f'agave_{name}_{width}' for name in ['g','transpose','add_u16','compress_pre','batch'] for width in [8,16]} | {'agave_portable_g','agave_portable_compress_pre'}
XOF_SYMBOLS = ['agave_portable_compress_xof', 'agave_portable_compress_in_place']
XOF_SPANS = [
    ('lib.rs', 'IV', 'constant'), ('lib.rs', 'MSG_SCHEDULE', 'constant'),
    ('lib.rs', 'counter_low', 'function'), ('lib.rs', 'counter_high', 'function'),
    ('platform.rs', 'words_from_le_bytes_64', 'function'),
    ('platform.rs', 'le_bytes_from_words_64', 'function'),
    *[('portable.rs', name, 'function') for name in
      ['g', 'round', 'compress_pre', 'compress_xof', 'compress_in_place']],
]
def require(ok, message):
    if not ok: raise ValueError(message)
def digest(data): return hashlib.sha256(data).hexdigest()
def check_xof_source(gen, manifest, blake3):
    """Independently recover bounded, top-level declarations (not brace counting)."""
    harness = (gen/'portable_xof_harness.rs').read_text()
    spans = manifest['verbatim_spans']
    require([(s['file'],s['name'],s['kind']) for s in spans] == XOF_SPANS,
            'XOF source declaration inventory changed')
    pieces = {}
    for span in spans:
        name = span['name']
        if span['kind'] == 'constant':
            pattern = r'^const ' + re.escape(name) + r':.*?^\];'
        else:
            pattern = r'^(?:pub(?:\([^)]*\))? )?fn ' + re.escape(name) + r'\(.*?^\}'
        matches = list(re.finditer(pattern,harness,re.MULTILINE|re.DOTALL))
        require(len(matches)==1, f'XOF declaration missing/duplicated: {name}')
        fragment = matches[0].group().encode()
        require(digest(fragment)==span['sha256'], f'XOF source fragment changed: {name}')
        require(0 <= span['start_byte'] < span['end_byte'], f'invalid XOF source span: {name}')
        require(span['end_byte']-span['start_byte']==len(fragment), f'XOF span length changed: {name}')
        if blake3:
            source=(blake3/'src'/span['file']).read_bytes()
            require(span['end_byte']<=len(source), f'XOF span outside source: {name}')
            require(source[span['start_byte']:span['end_byte']]==fragment,
                    f'XOF source span differs: {name}')
        pieces[name] = fragment.decode()+'\n'
    def fn(name): return '#[inline(always)]\n'+pieces[name]
    expected='type CVWords = [u32; 8];\nconst BLOCK_LEN: usize = 64;\n'
    expected+=pieces['IV']+pieces['MSG_SCHEDULE']+fn('counter_low')+fn('counter_high')
    expected+='mod platform {\n'+fn('words_from_le_bytes_64')+fn('le_bytes_from_words_64')+'}\n'
    expected+=''.join(fn(name) for name in ['g','round','compress_pre','compress_xof','compress_in_place'])
    expected+='\n#[unsafe(no_mangle)]\npub fn agave_portable_compress_xof(cv:&CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8)->[u8;64] { compress_xof(cv,block,len,counter,flags) }\n#[unsafe(no_mangle)]\npub fn agave_portable_compress_in_place(cv:&mut CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8) { compress_in_place(cv,block,len,counter,flags); }\n'
    require(harness==expected, 'XOF harness scaffolding or call binding changed')

def verify(root, agave=None, blake3=None):
    lock=json.loads((root/'provenance.lock.json').read_text())
    preserved_keys={name+ext for name in BASE_SYMBOLS for ext in ['.lean']} | {'generated/'+name+'.mlir' for name in BASE_SYMBOLS}
    require(set(lock['preserved_regions_sha256'])==preserved_keys, 'original region preservation inventory changed')
    for name,expected in {**lock['files_sha256'], **lock['preserved_regions_sha256']}.items():
        require(digest((root/name).read_bytes())==expected, f'locked file changed: {name}')
    gen=root/'generated'
    m=json.loads((gen/'manifest.json').read_text())
    p=json.loads((gen/'portable_manifest.json').read_text())
    x=json.loads((gen/'portable_xof_manifest.json').read_text())
    require(m['agave_commit']==AGAVE and m['arch_sha256']==ARCH,'Agave pin changed')
    require(p['source_hashes']==BLAKE and x['source_hashes']==BLAKE,'BLAKE3 pins changed')
    require(x['symbols']==XOF_SYMBOLS,'XOF exports changed')
    require('release: 1.98.1\n' in m['rustc'] and 'LLVM version: 22.1.8\n' in m['rustc'],'unexpected Rust/LLVM version')
    require(m['mlir_translate'].startswith('Ubuntu LLVM version 22.1.8\n'),'unexpected MLIR version')
    require(p['commands'][0][0]==m['commands'][0][0] and p['commands'][1][0]==m['commands'][1][0],'portable compiler paths differ')
    require(x['rustc']==m['rustc'], 'XOF Rust compiler version changed')
    require(x['mlir_translate']==m['mlir_translate'], 'XOF MLIR compiler version changed')
    xc=x['commands']
    require(len(xc)==2 and xc[0][0]==m['commands'][0][0] and xc[1][0]==m['commands'][1][0],
            'XOF compiler paths changed')
    require(xc[0][1:-3]==['--edition=2024','--crate-type=lib','--crate-name=agave_portable_xof_extract',
            '--emit=llvm-ir','-C','opt-level=3','-C','panic=abort','-C','debug-assertions=no'],
            'XOF Rust command flags changed')
    require(xc[0][-2]=='-o' and pathlib.Path(xc[0][-3]).name=='portable_xof_harness.rs'
            and pathlib.Path(xc[0][-1]).name=='portable_xof.ll', 'XOF Rust command outputs changed')
    require(xc[1][1:3]==['--import-llvm','--mlir-print-op-generic'] and len(xc[1])==6
            and xc[1][3]==xc[0][-1] and xc[1][4]=='-o'
            and pathlib.Path(xc[1][5]).name=='portable_xof.mlir', 'XOF MLIR command changed')
    require(set(x['artifacts'])=={'portable_xof_harness.rs','portable_xof.ll','portable_xof.mlir'},
            'XOF artifact inventory changed')
    for manifest,field in [(m,'files_sha256'),(p,'artifacts'),(x,'artifacts')]:
        for name,expected in manifest[field].items():
            require(digest((gen/name).read_bytes())==expected,f'artifact hash mismatch: {name}')
    source=(gen/'arch.rs').read_bytes()[:m['source_prefix_bytes']]
    require(digest(source)==ARCH,'arch source prefix changed')
    if agave:
        for name,expected in AGAVE_FILES.items():
            require(digest((agave/name).read_bytes())==expected,f'supplied Agave source changed: {name}')
    if blake3:
        for name,expected in BLAKE.items():
            require(digest((blake3/'src'/name).read_bytes())==expected,f'supplied BLAKE3 source changed: {name}')
        harness=(gen/'portable_harness.rs').read_bytes()
        for span in p['verbatim_spans']:
            data=(blake3/'src'/span['file']).read_bytes()
            lo,hi=span['start_byte'],span['end_byte']
            require(0<=lo<hi<=len(data),'invalid portable source span')
            fragment=data[lo:hi]
            require(digest(fragment)==span['sha256'],'portable span hash differs')
            require(fragment in harness,'portable source span missing from harness')
    check_xof_source(gen,x,blake3)
    # Independently ensure each region preserves every instruction, type, block,
    # operand, constant and flag; only precisely shaped alias metadata is removed.
    combined='\n'.join((gen/name).read_text() for name in ['kernels.mlir','portable.mlir','portable_xof.mlir'])
    lines=combined.splitlines();symbols=[]
    for i,line in enumerate(lines):
        match=re.search(r'sym_name = "(agave_[^"]+)"',line)
        if not match: continue
        name=match[1];symbols.append(name)
        end=next(j for j in range(i+1,len(lines)) if lines[j]=='  }) : () -> ()')
        body=['{']+lines[i+1:end]+['}']
        clean=[]
        for instruction in body:
            instruction=re.sub(r'\b(?:alias_scopes|noalias_scopes) = \[(?:#alias_scope\d*(?:, )?)*\],? ?', '',instruction)
            clean.append(re.sub(r',\s*}>', '}>', instruction))
        require((gen/(name+'.mlir')).read_text()=='\n'.join(clean)+'\n',f'non-metadata region transformation: {name}')
    require(len(symbols)==14 and set(symbols)==BASE_SYMBOLS|set(XOF_SYMBOLS),'missing or duplicate exported kernel')
    require(set(symbols[-2:])==set(XOF_SYMBOLS),'separate XOF exports missing')
    # Independently decode the global as little-endian 64-bit words (the lifter
    # uses per-word int.from_bytes; this check uses struct's fixed-width parser).
    import struct
    global_name='alloc_61fb4a9344bbdaf2573accd6331d7e32'
    global_line=next(line for line in lines if '"llvm.mlir.global"' in line and f'sym_name = "{global_name}"' in line)
    encoded=re.search(r'value = "([^"]*)"',global_line).group(1)
    require(re.fullmatch(r'(?:\\[0-9A-Fa-f]{2}){896}',encoded) is not None,'invalid schedule literal')
    raw=bytes.fromhex(encoded.replace('\\',''))
    expected_words=list(struct.unpack('<112Q',raw))
    schedule=json.loads((gen/'schedule.json').read_text())
    require(schedule=={'symbol':global_name,'initializer_sha256':digest(raw),'words_le64':expected_words},'schedule global decoding changed')
    # Regenerate only in a temporary directory. Compare every output byte; never
    # update checked-in manifests, regions, Lean definitions or inventories.
    with tempfile.TemporaryDirectory(prefix='agave-provenance-') as td:
        temp=pathlib.Path(td);(temp/'generated').mkdir()
        for name in ['kernels.mlir','portable.mlir','portable_xof.mlir']:
            shutil.copyfile(gen/name,temp/'generated'/name)
        subprocess.run([sys.executable,str(root/'lift.py'),str(temp)],check=True,capture_output=True)
        for f in temp.rglob('*'):
            if f.is_file():
                relative=f.relative_to(temp)
                require((root/relative).read_bytes()==f.read_bytes(),f'lift output changed: {relative}')
    return len(symbols)
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--directory',type=pathlib.Path,default=ROOT)
    p.add_argument('--agave',type=pathlib.Path)
    p.add_argument('--blake3',type=pathlib.Path)
    a=p.parse_args()
    try: n=verify(a.directory,a.agave,a.blake3)
    except (ValueError,OSError,KeyError,IndexError,TypeError,StopIteration,subprocess.CalledProcessError) as e:
        print(f'FAIL: {e}',file=sys.stderr);return 1
    print(f'OK: pinned sources, compiler versions, artifact hashes and {n} regenerated Lean/MLIR regions');return 0
if __name__=='__main__': sys.exit(main())
