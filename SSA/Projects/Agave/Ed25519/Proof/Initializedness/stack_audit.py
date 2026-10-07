#!/usr/bin/env python3
"""Conservative byte-write CFG audit of literal imported RIR regions.

This is an evidence generator, not a Lean certificate or LLVM verifier. Calls
remain explicit boundaries: no write effect is inferred from sret/readonly
attributes. Dynamic offsets, unknown pointer aliases and cyclic initializations
remain unresolved. Copied bytes inherit source write coverage. Both branch
successors are considered, so a reported gap need not be feasible. The static
pass resets masks at lifetime markers but does not propagate scalar undef/poison
or resolve pointer block arguments; it is not a proof even for a covered read.
"""
import argparse, collections, hashlib, json, pathlib, re

BASE = pathlib.Path(__file__).resolve().parents[2]
REPO = next(p for p in BASE.parents if (p / 'lakefile.lean').exists() or (p / 'lakefile.toml').exists())
REG = r'%[A-Za-z0-9_.$]+'


def width(ty):
    ty = ty.strip()
    if re.fullmatch(r'i\d+', ty): return (int(ty[1:]) + 7) // 8
    m = re.fullmatch(r'(?:vector|!llvm.array)<(\d+)\s*x\s*(.+)>', ty)
    if m:
        w = width(m[2]); return None if w is None else int(m[1])*w
    return None


def intervals(xs):
    result=[]
    for x in sorted(xs):
        if result and x == result[-1][1]: result[-1][1] += 1
        else: result.append([x,x+1])
    return result


def regions(path):
    lines=path.read_text().splitlines(); ns=[]; i=0
    while i < len(lines):
        line=lines[i]
        m=re.match(r'namespace (\S+)',line)
        if m: ns.append(m[1])
        m=re.match(r'end (\S+)',line)
        if m and ns and ns[-1]==m[1]: ns.pop()
        m=re.match(r'(?:execution_def|mlir_def) (\w+)',line)
        if m:
            begin=i; name='.'.join(ns+[m[1]])
            while i<len(lines) and not lines[i].rstrip().endswith('{'): i+=1
            body=[]; i+=1
            while i<len(lines) and not lines[i].startswith('}'):
                body.append((i+1,lines[i])); i+=1
            yield name,begin+1,body
        i+=1


def analyze(path,name,line,body):
    blocks={}; block=None; constants={}; ptrs={}; allocs={}; operations=[]
    for ln,text in body:
        b=re.match(r'\s*\^(bb\d+)(?:\((.*?)\))?:',text)
        if b:
            block=b[1]; blocks[block]=[]
            for reg,ty in re.findall(r'('+REG+r'): ([^,]+)',b[2] or ''):
                if ty.strip()=='!llvm.ptr' and block=='bb0': ptrs[reg]={('external:'+reg,0)}
            continue
        m=re.match(r'\s*(?:('+REG+r') = )?"(llvm\.[^"]+)"\(([^)]*)\)(.*)',text)
        if not m or block is None: continue
        dst,op,args,rest=m.groups(); args=re.findall(REG,args)
        instr=dict(line=ln,dst=dst,op=op,args=args,rest=rest,text=text.strip(),block=block)
        blocks[block].append(instr); operations.append(instr)
        if op=='llvm.mlir.constant':
            c=re.search(r'value = (-?\d+) : i\d+',rest)
            if c: constants[dst]=int(c[1])
        if op=='llvm.mlir.addressof': ptrs[dst]={('global:'+dst,0)}
        if op=='llvm.alloca':
            ty=re.search(r'elem_type = (.+?)(?:,|}>|\}\s*>|\}>\s*:)',rest)
            n=width(ty[1]) if ty else None
            count=constants.get(args[0]) if args else None
            size=n*count if n is not None and count is not None else None
            allocs[dst]=dict(register=dst,line=ln,bytes=size)
            ptrs[dst]={(dst,0)}
    # Constant aliases; unknown arithmetic indices preserve object identity.
    for _ in range(len(operations)+1):
        changed=False
        for x in operations:
            if x['op']!='llvm.getelementptr' or not x['args']: continue
            bases=ptrs.get(x['args'][0],set()); indices=x['args'][1:]
            raw=re.search(r'rawConstantIndices = array<i32: ([^>]+)>',x['rest'])
            vals=[]; cur=iter(indices)
            if raw:
                for v in raw[1].split(','):
                    v=int(v.strip()); vals.append(constants.get(next(cur,'')) if v==-2147483648 else v)
            et=re.search(r'elem_type = (.+?), (?:noWrapFlags|rawConstantIndices)',x['rest'])
            typ=et[1] if et else None
            if typ=='i8' and len(vals)==1: off=vals[0]
            elif typ and re.fullmatch(r'i\d+',typ) and len(vals)==1:
                off=None if vals[0] is None else width(typ)*vals[0]
            elif typ and (arr:=re.fullmatch(r'!llvm.array<(\d+) x (i\d+)>',typ)) and len(vals)==2:
                off=None if None in vals else width(arr[2])*(int(arr[1])*vals[0]+vals[1])
            elif vals and all(v==0 for v in vals): off=0
            else: off=None
            new={(root,None if base is None or off is None else base+off) for root,base in bases}
            if new != ptrs.get(x['dst'],set()):ptrs[x['dst']]=new;changed=True
        if not changed: break
    if 'bb0' not in blocks:
        return dict(name=name,file=str(path.relative_to(REPO)),line=line,blocks=len(blocks),reachable_blocks=[],allocations=list(allocs.values()),local_reads_checked=[],unresolved_reads=[],unresolved_calls=[],unknown_pointer_reads=[],dataflow_iterations=0,converged=False,parse_error='No bb0 entry block recognized')
    succ={b:set() for b in blocks}; pred={b:set() for b in blocks}
    for b,ins in blocks.items():
        if ins:
            succ[b]=set(re.findall(r'\^(bb\d+)',ins[-1]['rest'])) & set(blocks)
            for c in succ[b]:pred[c].add(b)
    reachable={'bb0'}; queue=['bb0']
    while queue:
        for c in succ.get(queue.pop(),[]):
            if c not in reachable:reachable.add(c);queue.append(c)
    top={r:set(range(a['bytes'] or 0)) for r,a in allocs.items()}
    incoming={b:{r:set(v) for r,v in top.items()} for b in reachable}; outgoing={}
    incoming['bb0']={r:set() for r in allocs}; findings=[]; checked=[]; calls=[]; unknown=[]

    def transfer(b,state,record=False):
        state={r:set(v) for r,v in state.items()}
        def read(reg,n,x,kind):
            candidates=ptrs.get(reg,set())
            if not candidates:
                if record:unknown.append(dict(line=x['line'],operation=kind,pointer=reg,reason='unresolved pointer provenance'))
                return set()
            masks=[]
            for root,off in candidates:
                if root not in allocs:
                    masks.append(set(range(n or 0)));continue
                covered=state[root]
                gap=None if n is None or off is None else set(range(off,off+n))-covered
                rec=dict(line=x['line'],block=b,operation=kind,pointer=reg,allocation=root,offset=off,bytes=n)
                if record:
                    if gap is None:findings.append(dict(rec,status='unresolved_dynamic_range'))
                    elif gap:findings.append(dict(rec,status='not_definitely_written',missing=intervals(gap)))
                    else:checked.append(dict(rec,status='covered_by_local_writes'))
                masks.append(set() if n is None or off is None else {j for j in range(n) if off+j in covered})
            return set.intersection(*masks) if masks else set()
        def write(reg,n,mask):
            candidates=ptrs.get(reg,set())
            if len(candidates)!=1:return
            root,off=next(iter(candidates))
            if root not in allocs or off is None or n is None:return
            state[root].difference_update(range(off,off+n))
            state[root].update(off+j for j in mask if 0<=off+j<(allocs[root]['bytes'] or 0))
        for x in blocks[b]:
            op=x['op'];args=x['args'];rest=x['rest']
            if op=='llvm.alloca':state[x['dst']]=set()
            elif op in ('llvm.load','llvm.load_atomic'):
                ty=rest.split(' -> ')[-1].strip();read(args[0],width(ty),x,'load')
            elif op=='llvm.store':
                ty=re.search(r': \((.*), !llvm.ptr\) ->',rest)
                n=width(ty[1]) if ty else None;write(args[1],n,set(range(n or 0)))
            elif op=='llvm.intr.memset':
                n=constants.get(args[2]);write(args[0],n,set(range(n or 0)))
            elif op=='llvm.intr.memcpy':
                n=constants.get(args[2]);mask=read(args[1],n,x,'memcpy-source');write(args[0],n,mask)
            elif op in ('llvm.intr.lifetime.start', 'llvm.intr.lifetime.end'):
                for a in args:
                    for root,_ in ptrs.get(a,set()):
                        if root in allocs:state[root]=set()
            elif op=='llvm.call':
                local={root for a in args for root,_ in ptrs.get(a,set()) if root in allocs}
                if record and local:
                    sym=re.search(r'callee = @([^,> ]+)',rest)
                    calls.append(dict(line=x['line'],block=b,callee=sym[1] if sym else None,allocations=sorted(local),reason='callee read/write effects not assumed'))
                # A callee may overwrite bytes with values whose provenance this local analysis cannot prove.
                for root in local:state[root]=set()
        return state
    for iteration in range(200):
        changed=False
        for b in sorted(reachable,key=lambda s:int(s[2:])):
            if b!='bb0':
                ps=[outgoing[p] for p in pred[b] if p in outgoing]
                if not ps:continue
                state={r:set.intersection(*(s[r] for s in ps)) for r in allocs}
                incoming[b]=state
            out=transfer(b,incoming[b])
            if out!=outgoing.get(b):outgoing[b]=out;changed=True
        if not changed:break
    for b in sorted(reachable):transfer(b,incoming[b],True)
    return dict(name=name,file=str(path.relative_to(REPO)),line=line,blocks=len(blocks),reachable_blocks=sorted(reachable),allocations=list(allocs.values()),local_reads_checked=checked,unresolved_reads=findings,unresolved_calls=calls,unknown_pointer_reads=unknown,dataflow_iterations=iteration+1,converged=not changed)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).with_name('static-report.json'));args=parser.parse_args()
    root_names=[
        'Bridge/CrossClientReadyUnderAudit.lean', 'Bridge/CrossClientGuardedCaller.lean',
        'Bridge/CrossClientCanonicalRAudit.lean', 'Bridge/CrossClientConcreteLeavesAudit.lean',
        'Bridge/CrossClientPointwiseDigestAudit.lean', 'Bridge/CrossClientSHACompleteAudit.lean',
        'Bridge/FiredancerSHAExecution/PointwiseVerifier.lean',
        'Bridge/CrossClientBackendReadyAudit.lean',
        'Proof/SHA512/Compression/FinalizationDispatchCompleteAudit.lean',
        'Proof/Encoding/DecompressExecution/DecoderSemanticAudit.lean',
        'Proof/Encoding/DecompressExecution/DecoderSemanticReadyAudit.lean',
        'Proof/Encoding/DecompressExecution/DecoderSqrtPrefixBridgeAudit.lean',
        'Proof/Encoding/DecompressValidPointAudit.lean']
    root_paths=[BASE/p for p in root_names]
    root_paths+=sorted((BASE/'Bridge/FiredancerSHAExecution').glob('*Audit.lean'))
    closure=set()
    def visit(p):
        if not p.exists() or p in closure:return
        closure.add(p)
        for imp in re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',p.read_text(),re.M):
            visit(REPO/(imp.replace('.','/')+'.lean'))
    for p in root_paths:visit(p)
    reports=[];hashes={}
    for path in sorted(BASE.rglob('*.lean')):
        if 'Initializedness' in path.parts:continue
        rs=list(regions(path))
        if not rs:continue
        hashes[str(path.relative_to(REPO))]=hashlib.sha256(path.read_bytes()).hexdigest()
        for r in rs:
            a=analyze(path,*r);a['root_import_reachable']=path in closure;reports.append(a)
    result=dict(format=1,requested_roots=[str(p.relative_to(REPO)) for p in root_paths],missing_roots=[str(p.relative_to(REPO)) for p in root_paths if not p.exists()],scope='All literal execution_def and mlir_def regions under Agave/Ed25519; import/call reachability requires separate review.',limitations=__doc__.strip(),source_sha256=hashes,regions=reports)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'files':len(hashes),'regions':len(reports),'root_import_reachable_regions':sum(r['root_import_reachable'] for r in reports),'allocations':sum(len(r['allocations']) for r in reports),'checked_local_reads':sum(len(r['local_reads_checked']) for r in reports),'unresolved_reads':sum(len(r['unresolved_reads']) for r in reports),'unresolved_calls':sum(len(r['unresolved_calls']) for r in reports),'nonconverged':[r['name'] for r in reports if not r['converged']]},indent=2))
if __name__=='__main__':main()
