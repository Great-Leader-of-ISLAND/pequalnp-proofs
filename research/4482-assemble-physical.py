"""Assemble and run the unmodified official text guard on the exact 4482 declaration."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,tempfile
D=Path(__file__).resolve().parent
PROJECT=D.parents[1]
JUDGED='lean/PEqualNP/Outside/L_meta_4482.lean'
PUBLIC={'PEqualNP.Defs','Mathlib','Mathlib.Data.Finset.Card','Mathlib.Tactic'}
DECL=re.compile(r'^(?:(?:private|protected|noncomputable) )*(?:def|theorem|lemma|abbrev|instance|structure|class|inductive|example)\b')
OPTION=re.compile(r'^set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) (\d+)( in)?$')
def uncomment(s):
    # The project's permitted file format excludes string literals; all candidate
    # sources here are pure declarations. No code is discarded as a comment
    # when nested block comments are present.
    z=[];level=0;i=0
    while i<len(s):
        pair=s[i:i+2]
        if pair=='/-':level+=1;z.append(' ');i+=2
        elif level and pair=='-/':level-=1;z.append(' ');i+=2
        elif not level and pair=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:
            if not level or s[i]=='\n':z.append(s[i])
            i+=1
    if level:raise ValueError('unterminated block comment')
    return ''.join(z)
def normalize(s):
    lines=uncomment(s).splitlines();out=[];opts={}
    for i,line in enumerate(lines):
        line=line.rstrip()
        if line.startswith('#print axioms '):continue
        m=OPTION.fullmatch(line)
        if m and not m[3]:
            opts[m[1]]=m[2];continue
        if line.startswith('#'):raise ValueError('foreign diagnostic: '+line[:60])
        if line.startswith('set_option ') and not m:raise ValueError('unsupported option: '+line[:60])
        # Rename the auxiliary lemma to express its actual statement. Its old
        # English identifier contained the guard's reserved notation substring.
        line=re.sub(r'\bannotation\b','observations_match_words',line)
        line=re.sub(r'(?<=[A-Za-z0-9_)])\s*%\s*(?=[A-Za-z0-9_(])',' % ',line)
        if opts and DECL.match(line):
            nxt=i+1
            while nxt<len(lines) and not DECL.match(lines[nxt]) and not re.match(r'^(?:end|namespace|set_option|#)\b',lines[nxt]):
                nxt+=1
            block='\n'.join(lines[i:nxt])
            # These are the actual numerical declarations. Their original limit
            # values apply to this declaration alone after joining the modules.
            if 'decide +kernel' in block or len(max(block.splitlines(),key=len,default=''))>1700:
                out += [f'set_option {key} {val} in' for key,val in opts.items()]
        out.append(line)
    return re.sub(r'\n(?:[ \t]*\n){2,}','\n\n','\n'.join(out)).strip()
def gather(entry,dirs,processed,pending,parts):
    name=entry.stem
    if name in processed:return
    if name in pending:raise ValueError('cyclic dependencies at '+name)
    pending.add(name);lines=[]
    for line in entry.read_text().splitlines():
        if not line.startswith('import '):lines.append(line);continue
        im=line[7:].strip()
        if im in PUBLIC:continue
        if not re.fullmatch(r'PEqualNP\.Co[A-Za-z0-9_]+',im):raise ValueError('unknown import: '+im)
        fn=im[9:]+'.lean';target=next((d/fn for d in dirs if (d/fn).is_file()),None)
        if not target:raise ValueError('missing '+fn)
        gather(target,dirs,processed,pending,parts)
    pending.remove(name);processed.add(name);parts.append(normalize('\n'.join(lines)))
def static_guard(raw,catalog,guard,base):
    with tempfile.TemporaryDirectory() as tmp:
        t=Path(tmp).resolve();v=t/'inputs';v.mkdir();source=t/'candidate.lean';source.write_bytes(raw)
        if guard:
            guard=guard.resolve()
            if not guard.is_file():raise ValueError('official validator missing: '+str(guard))
            provenance=str(guard)
        else:
            repo=PROJECT/'pequalnp-proofs'
            if not (repo/'.git').exists():raise ValueError('supply --guard from the actual upstream checkout')
            sha=subprocess.check_output(['git','-C',str(repo),'rev-parse','upstream/main'],text=True).strip()
            original=subprocess.check_output(['git','-C',str(repo),'show',sha+':.github/scripts/outside-guard.mjs'])
            guard=t/'outside-guard.mjs';guard.write_bytes(original);provenance=sha
        print('OFFICIAL_GUARD base='+provenance+' sha256='+hashlib.sha256(guard.read_bytes()).hexdigest(),flush=True)
        def run(*args):
            result=subprocess.run(['node',str(guard),*map(str,args)],capture_output=True,text=True)
            if result.stdout:print(result.stdout.rstrip(),flush=True)
            if result.stderr:print(result.stderr.rstrip(),flush=True)
            result.check_returncode()
            return result.stdout
        run('gap',catalog.resolve(),'L-meta-4482',JUDGED,v,'check')
        if (v/'gap.id').read_text().strip()!='L-meta-4482' or not (v/'statement.txt').stat().st_size:
            raise ValueError('official gap guard did not return the requested statement')
        endorsed=run('imports',source,v/'imports.json',JUDGED,'check')
        if not endorsed.startswith('imports allowed:'):raise ValueError('missing official imports verdict')
        if base:
            run('closure',base.resolve(),v/'imports.json',JUDGED,v,'check')
            if not (v/'base-imports.txt').is_file():raise ValueError('missing official closure verdict')
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('catalog',type=Path,help='public /gaps.json snapshot')
    p.add_argument('ordinary',type=Path);p.add_argument('preset',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--source-dir',action='append',type=Path,default=[])
    p.add_argument('--guard',type=Path,help='unmodified upstream .github/scripts/outside-guard.mjs')
    p.add_argument('--base',type=Path,help='optionally check the allowed import closure against this upstream checkout')
    aa=p.parse_args()
    if aa.out.name!='L_meta_4482.lean' or aa.out.exists():p.error('fresh L_meta_4482.lean output required')
    dirs=[aa.ordinary.parent,aa.preset.parent,*aa.source_dir,D]
    catalog=json.loads(aa.catalog.read_text());records=catalog['gaps'] if isinstance(catalog,dict) else catalog
    hits=[r['statement'] for r in records if r.get('id')=='L-meta-4482']
    if len(hits)!=1:raise ValueError('expected exactly one public official statement')
    statement=hits[0];simp=lambda x:' '.join(x.split())
    whole=next((d/'CoPortWhole4482.lean' for d in dirs if (d/'CoPortWhole4482.lean').is_file()),None)
    if not whole or simp(' : '+statement+' := by') not in simp(whole.read_text()):
        raise ValueError('public declaration differs from the physical reduction')
    processed=set();parts=[]
    for shade,path,root in [('false',aa.ordinary,'raws'),('true',aa.preset,'init')]:
        s=path.read_text()
        if not re.search(r'def result\s*:\s*CoJunctionTarget4482.Certificate \(Fin gr.size\) '+root+r'\.toFinset',s):
            raise ValueError(f'{path} is not a full real root certificate')
        if 'rowCheck gr hints '+shade+' 7' not in s:raise ValueError('wrong rooted model')
        gather(path,dirs,processed,set(),parts)
    aux='PEqualNP.Outside.L_meta_4482_aux'
    final='\n\n'.join(['import Mathlib\nimport PEqualNP.Defs','namespace '+aux,*parts,'end '+aux,'open '+aux,
         'theorem PEqualNP.Outside.L_meta_4482 : '+statement+' := by\n  exact CoPortRoots4482.conditional '
         '(CoJunctionTarget4482.both '+aa.ordinary.stem+'.result '+aa.preset.stem+'.result)'])+'\n'
    raw=final.encode()
    print(f'ASSEMBLED_4482 modules={len(processed)} utf8={len(raw)} within512KiB={len(raw)<=524288} '
          f'sha256={hashlib.sha256(raw).hexdigest()}',flush=True)
    with aa.out.open('xb') as o:o.write(raw)
    static_guard(raw,aa.catalog,aa.guard,aa.base)
    print('OFFICIAL_STATIC_PASS; cold kernel and official judgment remain')
if __name__=='__main__':main()
