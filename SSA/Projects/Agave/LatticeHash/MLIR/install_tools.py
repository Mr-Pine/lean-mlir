#!/usr/bin/env python3
"""Unpack verified LLVM 22.1.8 Ubuntu Noble tools locally, without root."""
import argparse,hashlib,pathlib,urllib.request,subprocess
p=argparse.ArgumentParser();p.add_argument('directory',type=pathlib.Path);a=p.parse_args();a.directory.mkdir(parents=True,exist_ok=True)
packages={
'libmlir-22': 'd0b83628ac37b4d22a9c492bd90585e4b1849a39b099ad8632e43a2c3760406b',
'libllvm22': 'e94d23161316c53ebe8c9e35038468e06a5e47dbdf207a3c54a22ab40e37cbb6',
'mlir-22-tools':'bcc7cb152841ba9db8c737eba8f27e34aaa1d7f0d647f35f995630c887c8d60b',
}
# The exact package index used for this extraction is retained with its checksum.
import gzip
index=gzip.decompress(urllib.request.urlopen('https://apt.llvm.org/noble/dists/llvm-toolchain-noble-22/main/binary-amd64/Packages.gz').read()).decode()
for chunk in index.split('\n\n'):
 f=dict(line.split(': ',1) for line in chunk.splitlines() if ': ' in line and not line.startswith(' '))
 if f.get('Package') not in ['libllvm22','libmlir-22','mlir-22-tools']:continue
 if f['Package'] in packages: assert f['SHA256']==packages[f['Package']], 'Package index changed; inspect before updating pin'
 name=pathlib.Path(f['Filename']).name;dest=a.directory/name
 urllib.request.urlretrieve('https://apt.llvm.org/noble/'+f['Filename'],dest)
 assert hashlib.sha256(dest.read_bytes()).hexdigest()==f['SHA256']
 subprocess.run(['dpkg-deb','-x',str(dest),str(a.directory/'root')],check=True)
