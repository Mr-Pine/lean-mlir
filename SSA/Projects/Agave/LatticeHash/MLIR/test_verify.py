#!/usr/bin/env python3
"""Mutation checks for the provenance boundary, without a compiler."""
import pathlib,shutil,subprocess,sys,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parent
class ProvenanceMutations(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='agave-provenance-test-')
        self.root=pathlib.Path(self.temp.name)
        for f in ROOT.glob('*.py'):shutil.copyfile(f,self.root/f.name)
        for f in ROOT.glob('agave_*.lean'):shutil.copyfile(f,self.root/f.name)
        shutil.copyfile(ROOT/'GeneratedGlobals.lean',self.root/'GeneratedGlobals.lean')
        shutil.copyfile(ROOT/'provenance.lock.json',self.root/'provenance.lock.json')
        shutil.copytree(ROOT/'generated',self.root/'generated')
    def tearDown(self):self.temp.cleanup()
    def check(self,success,*args):
        result=subprocess.run([sys.executable,str(self.root/'verify.py'),*args],capture_output=True,text=True)
        self.assertEqual(result.returncode==0,success,result.stdout+result.stderr)
    def test_pristine(self):self.check(True)
    def test_mutations(self):
        cases=[('generated/arch.rs',b'v[a] =',b'v[b] ='),
               ('generated/kernels.ll',b'add <',b'xor <'),
               ('generated/kernels.mlir',b'"llvm.add"',b'"llvm.xor"'),
               ('generated/portable_harness.rs',b'wrapping_add',b'wrapping_sub'),
               ('generated/portable.ll',b' add ',b' sub '),
               ('generated/portable.mlir',b'"llvm.add"',b'"llvm.sub"'),
               ('generated/portable_xof_harness.rs',b'state[0] ^= state[8]',b'state[0] ^= state[9]'),
               ('generated/portable_xof.ll',b' xor ',b' add '),
               ('generated/portable_xof.mlir',b'"llvm.xor"',b'"llvm.add"'),
               ('generated/portable_xof_manifest.json',b'1.98.1',b'1.97.1'),
               ('agave_portable_compress_xof.lean',b'"llvm.xor"',b'"llvm.add"'),
               ('agave_portable_compress_in_place.lean',b'"llvm.xor"',b'"llvm.add"'),
               ('agave_g_8.lean',b'"llvm.add"',b'"llvm.xor"'),
               ('generated/agave_g_8.mlir',b'"llvm.add"',b'"llvm.xor"'),
               ('generated/manifest.json',b'1.98.1',b'1.97.1'),
               ('GeneratedGlobals.lean',b'0#64',b'1#64'),
               ('generated/schedule.json',b'words_le64',b'words_be64'),
               ('lift.py',b'Only alias',b'Changed alias')]
        for name,before,after in cases:
            with self.subTest(file=name):
                f=self.root/name;original=f.read_bytes();self.assertIn(before,original)
                f.write_bytes(original.replace(before,after,1))
                self.check(False);f.write_bytes(original)
    def test_last_alias_metadata_keeps_valid_attribute_dictionary(self):
        # A final alias attribute must not leave a dangling comma after erasure.
        with tempfile.TemporaryDirectory(prefix='agave-lift-regression-') as td:
            root=pathlib.Path(td);(root/'generated').mkdir()
            source='\n'.join([
                '  "llvm.func"() <{sym_name = "agave_metadata_case"}> ({',
                '  ^bb0(%arg0: !llvm.ptr):',
                '    %0 = "llvm.load"(%arg0) <{alignment = 1 : i64, isVolatile = false, alias_scopes = [#alias_scope1], noalias_scopes = [#alias_scope2]}> : (!llvm.ptr) -> i8',
                '    "llvm.return"() : () -> ()',
                '  }) : () -> ()', ''])
            (root/'generated/kernels.mlir').write_text(source)
            subprocess.run([sys.executable,str(self.root/'lift.py'),str(root)],check=True)
            region=(root/'generated/agave_metadata_case.mlir').read_text()
            self.assertIn('<{alignment = 1 : i64, isVolatile = false}>',region)
            self.assertNotIn(', }>',region)
            self.assertNotIn('alias_scope',region)
            self.assertIn('"llvm.load"(%arg0)',region)
    def test_supplied_parent_source_edit(self):
        agave=self.root/'external_agave'
        (agave/'lattice-hash/src/batch').mkdir(parents=True)
        import json
        manifest=json.loads((self.root/'generated/manifest.json').read_text())
        source=(self.root/'generated/arch.rs').read_bytes()[:manifest['source_prefix_bytes']]
        (agave/'lattice-hash/src/batch/arch.rs').write_bytes(source)
        (agave/'lattice-hash/src/batch.rs').write_text('changed parent layout')
        self.check(False,'--agave',str(agave))
    def test_mixed_portable_argument_order(self):
        text=(self.root/'agave_portable_g.lean').read_text()
        self.assertIn('Ctxt.ofList [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr]',text)
    def test_regeneration_detects_lean_edit(self):
        # New XOF Lean outputs are checked by regeneration, not individually locked.
        f=self.root/'agave_portable_compress_xof.lean';f.write_bytes(f.read_bytes().replace(b'"llvm.add"',b'"llvm.xor"',1))
        self.check(False)
    def test_original_twelve_regions_preserved(self):
        import json,hashlib
        lock=json.loads((self.root/'provenance.lock.json').read_text())
        self.assertEqual(len(lock['preserved_regions_sha256']),24)
        for name,expected in lock['preserved_regions_sha256'].items():
            self.assertEqual(hashlib.sha256((self.root/name).read_bytes()).hexdigest(),expected,name)
        regions=json.loads((self.root/'generated/regions.json').read_text())
        self.assertEqual(len(regions),14)
        self.assertEqual({r['symbol'] for r in regions[-2:]},
                         {'agave_portable_compress_xof','agave_portable_compress_in_place'})
    def test_xof_independent_checks_survive_rehashed_manifest(self):
        # Updating artifact hashes cannot hide a source/scaffold/command change.
        import json,hashlib
        manifest_path=self.root/'generated/portable_xof_manifest.json'
        lock_path=self.root/'provenance.lock.json'
        harness_path=self.root/'generated/portable_xof_harness.rs'
        original_manifest=manifest_path.read_bytes()
        original_lock=lock_path.read_bytes()
        original_harness=harness_path.read_bytes()
        for mutation in ['body','wrapper','command','span']:
            with self.subTest(mutation=mutation):
                manifest=json.loads(original_manifest)
                lock=json.loads(original_lock)
                harness=original_harness
                if mutation=='body':
                    harness=harness.replace(b'state[0] ^= state[8]',b'state[0] ^= state[9]',1)
                elif mutation=='wrapper':
                    harness=harness.replace(b'{ compress_xof(cv,block,len,counter,flags) }',
                                            b'{ compress_xof(cv,block,len,counter,flags ^ 1) }',1)
                elif mutation=='command':
                    manifest['commands'][0][6]='opt-level=0'
                else:
                    manifest['verbatim_spans'][-1]['end_byte']+=1
                harness_path.write_bytes(harness)
                manifest['artifacts']['portable_xof_harness.rs']=hashlib.sha256(harness).hexdigest()
                manifest_path.write_text(json.dumps(manifest,indent=2)+'\n')
                lock['files_sha256']['generated/portable_xof_manifest.json']=hashlib.sha256(manifest_path.read_bytes()).hexdigest()
                lock_path.write_text(json.dumps(lock,indent=2)+'\n')
                self.check(False)
                manifest_path.write_bytes(original_manifest)
                lock_path.write_bytes(original_lock)
                harness_path.write_bytes(original_harness)
if __name__=='__main__':unittest.main()
