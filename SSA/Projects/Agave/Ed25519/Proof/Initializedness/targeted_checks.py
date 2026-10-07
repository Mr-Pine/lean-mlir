#!/usr/bin/env python3
"""Targeted byte-definedness execution of actual scalar imported MLIR regions.

This independent Python interpreter is not a verified RIR/LLVM interpreter.
It fails on unknown opcodes, checks ordinary-load definedness, propagates byte
masks through memcpy, and resets masks on lifetime.start. Overflow/alignment
are not independently checked. Challenge compression is a boundary observer;
its finalizer callback models the separately proved padding-store algorithm.
All four Firedancer regions are executed directly, including all 80 rounds;
transcript outputs are checked against hashlib.sha512.
"""
import hashlib, json, pathlib, re
from stack_audit import BASE, REPO, REG, regions, width


def parse(path, suffix):
    name,line,body=next(r for r in regions(path) if r[0].endswith(suffix))
    blocks={};params={};b=None
    for ln,text in body:
        m=re.match(r'\s*\^(bb\d+)(?:\((.*?)\))?:',text)
        if m:
            b=m[1];blocks[b]=[];params[b]=re.findall(r'('+REG+r'): ',m[2] or '');continue
        m=re.match(r'\s*(?:('+REG+r') = )?"(llvm\.[^"]+)"\(([^)]*)\)(.*)',text)
        if m and b:blocks[b].append((ln,m[1],m[2],re.findall(REG,m[3]),m[4]))
    return name,blocks,params


class Machine:
    def __init__(self, fill):self.fill=fill;self.mem={};self.reg={};self.gaps=[];self.loads=0;self.copies=0;self.steps=0;self.blocks=[];self.observed=[];self.alloc_index=0
    def alloc(self,name,n,defined=False,data=None):
        self.mem[name]=[bytearray([self.fill]*n) if data is None else bytearray(data),[defined]*n,True]
        return (name,0)
    def span(self,p,n):
        root,off=p;data,mask,live=self.mem[root]
        assert live and 0<=off and off+n<=len(data),(root,off,n,'invalid access')
        return data,mask,off
    def read(self,p,n,ln,copy=False):
        data,mask,o=self.span(p,n);holes=[j for j in range(n) if not mask[o+j]]
        if holes:
            if not copy:raise AssertionError(('undefined ordinary load',ln,p,n,holes))
            self.gaps.append(dict(line=ln,source=p,bytes=n,missing_offsets=holes))
        if copy:self.copies+=1
        else:self.loads+=1
        return bytes(data[o:o+n]),list(mask[o:o+n])
    def write(self,p,data,mask=None):
        dst,dm,o=self.span(p,len(data));dst[o:o+len(data)]=data;dm[o:o+len(data)]=[True]*len(data) if mask is None else mask
    def execute(self, parsed, args, globals_map, callback=None):
        _,blocks,params=parsed;self.reg.update(zip(params['bb0'],args));b='bb0'
        for fuel in range(100000):
            self.blocks.append(b);jump=None
            for ln,dst,op,rs,rest in blocks[b]:
                self.steps+=1;args=[self.reg[x] for x in rs];out=None
                ty=rest.split(' -> ')[-1].strip();bits=int(ty[1:]) if re.fullmatch(r'i\d+',ty) else None
                if op=='llvm.mlir.constant':
                    m=re.search(r'value = (-?\d+) : i(\d+)',rest);out=int(m[1])%(1<<int(m[2]))
                elif op=='llvm.mlir.addressof':out=globals_map[re.search(r'global_name = @([^}]+)',rest)[1].strip().strip('"')]
                elif op=='llvm.alloca':
                    elem=re.search(r'elem_type = (.+?)\}>',rest)[1];out=self.alloc(f'alloc{self.alloc_index}:{dst}',width(elem)*args[0]);self.alloc_index+=1
                elif op=='llvm.getelementptr':
                    typ=re.search(r'elem_type = (.+?), (?:noWrapFlags|rawConstantIndices)',rest)[1]
                    raw=[int(x) for x in re.search(r'rawConstantIndices = array<i32: ([^>]+)>',rest)[1].split(',')]
                    dyn=iter(args[1:]);idx=[next(dyn) if x==-2147483648 else x for x in raw]
                    if typ=='i8':off=sum(idx)
                    elif re.fullmatch(r'i\d+',typ):off=width(typ)*idx[0]
                    elif (m:=re.fullmatch(r'!llvm.array<(\d+) x (i\d+)>',typ)):
                        off=width(m[2])*(int(m[1])*idx[0]+idx[1])
                    else:raise AssertionError(('unsupported GEP type',typ,ln))
                    out=(args[0][0],args[0][1]+off)
                elif op=='llvm.load':out=int.from_bytes(self.read(args[0],width(ty),ln)[0],'little')
                elif op=='llvm.store':
                    t=re.search(r': \((i\d+), !llvm.ptr\)',rest)[1];self.write(args[1],args[0].to_bytes(width(t),'little'))
                elif op=='llvm.intr.memcpy':
                    data,mask=self.read(args[1],args[2],ln,True);self.write(args[0],data,mask)
                elif op=='llvm.intr.memset':self.write(args[0],bytes([args[1]])*args[2])
                elif op=='llvm.intr.lifetime.start':
                    root,_=args[0];self.mem[root][1]=[False]*len(self.mem[root][1]);self.mem[root][2]=True
                elif op=='llvm.intr.lifetime.end':self.mem[args[0][0]][2]=False
                elif op in ('llvm.intr.experimental.noalias.scope.decl','llvm.fence'):pass
                elif op=='llvm.intr.assume':assert args[0],('assume',ln)
                elif op in ('llvm.zext','llvm.trunc'):out=args[0]
                elif op=='llvm.add':out=args[0]+args[1]
                elif op=='llvm.sub':out=args[0]-args[1]
                elif op=='llvm.mul':out=args[0]*args[1]
                elif op=='llvm.and':out=args[0]&args[1]
                elif op=='llvm.or':out=args[0]|args[1]
                elif op=='llvm.xor':out=args[0]^args[1]
                elif op=='llvm.lshr':out=args[0]>>args[1]
                elif op=='llvm.shl':out=args[0]<<args[1]
                elif op=='llvm.intr.bswap':out=int.from_bytes(args[0].to_bytes(width(ty),'little'),'big')
                elif op=='llvm.intr.fshl':
                    n=bits;k=args[2]%n;out=((args[0]<<k)|(args[1]>>(n-k))) if k else args[0]
                elif op=='llvm.icmp':
                    pred=int(re.search(r'predicate = (\d+)',rest)[1]);a,c=args
                    if pred==0:out=a==c
                    elif pred==1:out=a!=c
                    elif pred==6:out=a<c
                    elif pred==7:out=a<=c
                    elif pred==8:out=a>c
                    elif pred==9:out=a>=c
                    elif pred in (2,3,4,5):
                        n=int(re.search(r': \(i(\d+),',rest)[1]);a=a-(1<<n) if a>=1<<(n-1) else a;c=c-(1<<n) if c>=1<<(n-1) else c
                        out={2:a<c,3:a<=c,4:a>c,5:a>=c}[pred]
                    else:raise AssertionError(('predicate',pred))
                elif op=='llvm.call':
                    assert callback is not None,('unexpected external call',ln)
                    callback(self,re.search(r'callee = @([^, ]+)',rest)[1],args,ln)
                elif op=='llvm.br':jump=(re.findall(r'\^(bb\d+)',rest)[0],args);break
                elif op=='llvm.cond_br':
                    dests=re.findall(r'\^(bb\d+)',rest);seg=[int(x) for x in re.search(r'operandSegmentSizes = array<i32: ([^>]+)>',rest)[1].split(',')]
                    jump=(dests[0],args[1:1+seg[1]]) if args[0] else (dests[1],args[1+seg[1]:]);break
                elif op=='llvm.return':return args
                else:raise AssertionError(('unsupported opcode',op,ln))
                if dst is not None:self.reg[dst]=int(out)%(1<<bits) if bits is not None else out
            assert jump is not None,('block without exit',b)
            b,vals=jump;self.reg.update(zip(params[b],vals))
        raise AssertionError('fuel exhausted')


def challenge_callback(m,name,args,ln):
    if name.endswith('compress512'):
        chain,data,count=args;m.read(chain,64,ln)
        raw,_=m.read(data,128*count,ln);m.observed.append(raw)
        # Concrete total callback, solely to keep the defined chain initialized.
        m.write(chain,hashlib.sha512(m.read(chain,64,ln)[0]+raw).digest())
    elif name.endswith('scalar_from_sha512'):
        out,ctx=args;raw,mask=m.read(ctx,208,ln,True)
        count=int.from_bytes(m.read((ctx[0],ctx[1]+127),1,ln)[0],'little')
        assert count<128
        m.read((ctx[0],ctx[1]+128),64,ln);m.read((ctx[0],ctx[1]+192),16,ln)
        pending=m.read(ctx,count,ln)[0]
        blocks=int.from_bytes(raw[192:208],'little');length=((blocks*128+count)*8)%(1<<128)
        pad=pending+b'\x80'+bytes((111-count)%128)+length.to_bytes(16,'big')
        assert len(pad) in (128,256);m.observed.append(pad)
        m.write(out,hashlib.sha512(b''.join(m.observed)).digest()[:32])
    else:raise AssertionError(('unknown callback',name,ln))


def main():
    cp=BASE/'Proof/Verifier/ExecutionProgram.lean';fp=BASE/'Bridge/FiredancerSHAExecution/Program.lean'
    challenge=parse(cp,'.Challenge.program');core=parse(fp,'.Core.program')
    lengths=list(range(513))+[1023,1024,1025,4095,4096,4097,65535]
    fills=[0,0x55,0xaa,0xff];challenge_cases=0;gap_counts=set();paths=set()
    for n in lengths:
        observations=[]
        for fill in fills:
            m=Machine(fill);out=m.alloc('out',32);key=m.alloc('key',192,True,bytes((j*3)%256 for j in range(192)));sig=m.alloc('sig',64,True,bytes((j*5)%256 for j in range(64)));msg=m.alloc('msg',n,True,bytes((j*7)%256 for j in range(n)));iv=m.alloc('iv',64,True,bytes(range(64)))
            m.execute(challenge,[out,key,sig,msg,n],{'anon.2688bd6af3b9e90d4f6e608faea972d6.1':iv},challenge_callback)
            observations.append(m.read(out,32,0)[0]);gap_counts.add(len(m.gaps));paths.add(tuple(m.blocks));challenge_cases+=1
        assert len(set(observations))==1,('fill-dependent challenge boundary result',n)
    ll=BASE/'Bridge/FiredancerSHAExecution/generated/fd_sha512_core_ref.ll';text=ll.read_text();ks=[int(x)%(1<<64) for x in re.findall(r'i64 (-?\d+)',text.split('@fd_sha512_core_ref.K =',1)[1].split('align 16',1)[0])]
    assert len(ks)==80
    core_cases=0
    for count in [1,2,3,5]:
        results=[]
        for fill in fills:
            m=Machine(fill);chain=m.alloc('chain',64,True,bytes(range(64)));data=m.alloc('data',128*count,True,bytes((j*11)%256 for j in range(128*count)));kp=m.alloc('kp',640,True,b''.join(k.to_bytes(8,'little') for k in ks))
            m.execute(core,[chain,data,count],{'fd_sha512_core_ref.K':kp})
            assert not m.gaps;results.append(m.read(chain,64,0)[0]);core_cases+=1
        assert len(set(results))==1,('fill-dependent core output',count)
    init=parse(fp,'.Init.program');append=parse(fp,'.Append.program');finish=parse(fp,'.Finish.program')
    fd_cases=0;fd_paths=set();fd_lengths=list(range(258))+[1023,1024,1025,4095,4096]
    for n in fd_lengths:
        for fill in fills:
            m=Machine(fill);ctx=m.alloc('ctx',256);out=m.alloc('digest',64)
            rb=bytes(range(32));ab=bytes(range(32,64));mb=bytes((j*13)%256 for j in range(n))
            rp=m.alloc('R',32,True,rb);ap=m.alloc('A',32,True,ab);mp=m.alloc('M',n,True,mb)
            kp=m.alloc('kp',640,True,b''.join(k.to_bytes(8,'little') for k in ks))
            def fd_callback(m,name,args,ln):
                assert name=='fd_sha512_core_ref'
                saved=m.reg;m.reg={}
                m.execute(core,args,{'fd_sha512_core_ref.K':kp})
                m.reg=saved
            assert m.execute(init,[ctx],{})==[ctx]
            for p,length in [(rp,32),(ap,32),(mp,n)]:
                m.reg={};start=len(m.blocks)
                assert m.execute(append,[ctx,p,length],{},fd_callback)==[ctx]
                fd_paths.add(tuple(m.blocks[start:]))
            m.reg={};assert m.execute(finish,[ctx,out],{},fd_callback)==[out]
            assert not m.gaps,('Firedancer copied undefined bytes',n,fill,m.gaps)
            assert m.read(out,64,0)[0]==hashlib.sha512(rb+ab+mb).digest(),('digest mismatch',n,fill)
            fd_cases+=1
    report=dict(challenge_cases=challenge_cases,message_lengths=lengths,allocation_fill_patterns=fills,challenge_cfg_paths=[list(p) for p in sorted(paths)],challenge_uninitialized_copy_counts=sorted(gap_counts),challenge_ordinary_uninitialized_loads=0,core_cases=core_cases,core_block_counts=[1,2,3,5],core_ordinary_uninitialized_loads=0,core_fill_independent=True,firedancer_transcript_cases=fd_cases,firedancer_transcript_lengths=fd_lengths,firedancer_transcript_matches_hashlib=True,firedancer_uninitialized_reads_or_copies=0,limitations=__doc__.strip(),source_sha256={str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [cp,fp,ll]})
    pathlib.Path(__file__).with_name('targeted-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['message_lengths','firedancer_transcript_lengths','limitations','source_sha256']},indent=2))
if __name__=='__main__':main()
