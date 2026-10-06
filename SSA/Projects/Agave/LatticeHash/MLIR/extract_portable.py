#!/usr/bin/env python3
"""Compile byte-for-byte function spans from locked BLAKE3 portable source."""
import pathlib,argparse,hashlib,subprocess,json,re
p=argparse.ArgumentParser(); p.add_argument('--blake3',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--rustc',required=True);p.add_argument('--mlir-translate',required=True);a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
expected={'portable.rs':'85ed8cd8f601e6801c0a26358c7ac70e29759445cfe39c584f40af072a201601','lib.rs':'a187904c4b12ea7c100557c0f167cc91a034e391ddeb56c9db65f7d400a4b566','platform.rs':'954e3564bb976c333cfaa68fc672a8543afc2e021c8b89e8d9393816b0ad90d1'}
sources={k:(a.blake3/'src'/k).read_text() for k in expected}
for k,v in expected.items(): assert hashlib.sha256(sources[k].encode()).hexdigest()==v,k
spans=[]
def fn(file,name):
 s=sources[file]; start=s.index('fn '+name+'('); start=s.rfind('\n',0,start)+1
 if s[max(0,start-18):start].strip().startswith('#['): pass
 brace=s.index('{',start); depth=1; end=brace+1
 while depth:
  depth+=(s[end]=='{')-(s[end]=='}');end+=1
 spans.append({'file':file,'start_byte':start,'end_byte':end,'sha256':hashlib.sha256(s[start:end].encode()).hexdigest()})
 return '#[inline(always)]\n'+s[start:end]+'\n'
def const(name):
 s=sources['lib.rs'];start=s.index('const '+name+':');end=s.index('];',s.index('=',start))+2
 spans.append({'file':'lib.rs','start_byte':start,'end_byte':end,'sha256':hashlib.sha256(s[start:end].encode()).hexdigest()})
 return s[start:end]+'\n'
s='type CVWords = [u32; 8];\nconst BLOCK_LEN: usize = 64;\n'+const('IV')+const('MSG_SCHEDULE')+fn('lib.rs','counter_low')+fn('lib.rs','counter_high')
s+='mod platform {\n'+fn('platform.rs','words_from_le_bytes_64')+'}\n'
s+=fn('portable.rs','g')+fn('portable.rs','round')+fn('portable.rs','compress_pre')
s+='''
#[unsafe(no_mangle)]
pub fn agave_portable_g(v: &mut [u32;16], x:u32,y:u32) { g(v,0,4,8,12,x,y); }
#[unsafe(no_mangle)]
pub fn agave_portable_compress_pre(cv:&CVWords, block:&[u8;64], len:u8,counter:u64,flags:u8)->[u32;16] { compress_pre(cv,block,len,counter,flags) }
'''
rs=a.out/'portable_harness.rs';rs.write_text(s);ll=a.out/'portable.ll';mlir=a.out/'portable.mlir'
commands=[[a.rustc,'--edition=2024','--crate-type=lib','--crate-name=agave_portable_extract','--emit=llvm-ir','-C','opt-level=3','-C','panic=abort','-C','debug-assertions=no',str(rs),'-o',str(ll)],[a.mlir_translate,'--import-llvm','--mlir-print-op-generic',str(ll),'-o',str(mlir)]]
for cmd in commands:subprocess.run(cmd,check=True)
(a.out/'portable_manifest.json').write_text(json.dumps({'source_hashes':expected,'verbatim_spans':spans,'commands':commands,'artifacts':{x.name:hashlib.sha256(x.read_bytes()).hexdigest() for x in [rs,ll,mlir]},'boundary':'Exact function bodies/constants extracted from locked source, supplied type aliases, inline(always) attributes and exported wrappers; not complete BLAKE3 crate compilation.'},indent=2)+'\n')
