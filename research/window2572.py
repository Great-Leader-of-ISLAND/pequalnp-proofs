"""Bounded multi-output search. A zero error on the extreme rows implies full correctness."""
import argparse,json,random,time
from parallel2572 import N,X,rows,fa,fb,ga,gb,template,evaluate,agrees

def missing(v,a,b):return ((a & ~v)|(v & b)).bit_count()
def assess(gs):
    ws=evaluate(gs); fg=[missing(z,fa,fb) for z in ws]; gg=[missing(z,ga,gb) for z in ws]
    a=min(range(len(ws)),key=fg.__getitem__); b=min(range(len(ws)),key=gg.__getitem__)
    return fg[a],gg[b],a,b

def start(rng):
    xs,_,_=template(rng)
    i=rng.randrange(len(xs))
    _,a,b=xs[i];alias=rng.choice([a,b])
    def port(p):return alias if p==N+i else p-int(p>N+i)
    return [(op,port(a),port(b)) for j,(op,a,b) in enumerate(xs) if j!=i]

def mutate(gs,rng):
    ys=gs[:]
    for _ in range(1+int(rng.random()<.27)+int(rng.random()<.10)):
        i=rng.randrange(45);op,a,b=ys[i];k=rng.randrange(10)
        if k==0:op='and' if op=='or' else 'or'
        else:
            if k<5:a,b=b,a
            opts=[]
            if b>=N:opts+=list(ys[b-N][1:])
            for op2,p,q in ys[:i]:
                if p==a:opts.append(q)
                if q==a:opts.append(p)
            b=rng.choice(opts) if opts and rng.random()<.42 else rng.randrange(N+i)
        ys[i]=(op,a,b)
    return ys

def run(seconds,seed):
    rng=random.Random(seed);end=time.monotonic()+seconds;count=0;best=None;top=None;rank=None
    while time.monotonic()<end:
        gs=start(rng) if top is None or rng.random()<.55 else top[:]
        weight=rng.choice([1,2,3,4]);f,g,_,_=assess(gs);score=f+weight*g
        for _ in range(750):
            alt=mutate(gs,rng);f,g,a,b=assess(alt);count+=1
            if not f and not g:
                print('WITNESS',json.dumps({'gates':alt,'output':a,'observation':b}),flush=True);return
            mark=(f+g,max(f,g))
            if rank is None or mark<rank:rank=mark;best=(f,g);top=alt[:]
            val=f+weight*g
            if val<=score or rng.random()<.003:gs,score=alt,val
        if count%15000==0:print('tested',count,'minimum errors on the exact comparison rows',best,flush=True)
    print('BOUNDED search, no witness; tested',count,'best',best,'rows',len(rows),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=240);p.add_argument('--seed',type=int,default=2572)
    a=p.parse_args();run(a.seconds,a.seed)
