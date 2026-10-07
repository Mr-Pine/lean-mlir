#!/usr/bin/env python3
"""Build only this audit's new Lean modules and record exact input hashes.

Run from a mirror whose imported dependencies have already been built. This
script records dependency source hashes; it does not rebuild that dependency
closure or establish that copied dependency oleans were built from those hashes.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, time

HERE = pathlib.Path(__file__).resolve().parent
REPO = next(p for p in HERE.parents if (p/'lakefile.lean').exists() or (p/'lakefile.toml').exists())
MODULES = ['Observations', 'ShadowTrace', 'FiredancerRing', 'Audit']

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=pathlib.Path,default=HERE/'validation.json');args=parser.parse_args()
    env=dict(os.environ);env['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+env.get('PATH','')
    records=[];closure={}
    def visit(p):
        if not p.exists() or str(p.relative_to(REPO)) in closure:return
        closure[str(p.relative_to(REPO))]=sha(p)
        for imp in re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',p.read_text(),re.M):
            visit(REPO/(imp.replace('.','/')+'.lean'))
    for name in MODULES:
        src=HERE/(name+'.lean');visit(src)
        out=REPO/'.lake/build/lib/lean'/src.relative_to(REPO).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        cmd=['lake','env','lean','-j1','--tstack=400000','-o',str(out.relative_to(REPO)),str(src.relative_to(REPO))]
        begin=time.monotonic();proc=subprocess.run(cmd,cwd=REPO,env=env,capture_output=True,text=True)
        record=dict(module=name,command=cmd,exit_code=proc.returncode,seconds=round(time.monotonic()-begin,3),source_sha256=sha(src),stdout=proc.stdout,stderr=proc.stderr)
        if proc.returncode==0:record['olean_sha256']=sha(out)
        records.append(record);print(json.dumps(record),flush=True)
        if proc.returncode:break
    result=dict(repo=str(REPO),checked_modules=records,dependency_source_sha256=closure,dependency_freshness_limit=__doc__.strip())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    if any(r['exit_code'] for r in records) or len(records)!=len(MODULES):raise SystemExit(1)
if __name__=='__main__':main()
