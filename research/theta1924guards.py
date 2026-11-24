"""Necessary structural and derivative constraints for theta signed circuits of size ten."""
import itertools
from pathlib import Path
import argparse
import theta1924 as base


class Guarded(base.Encoding):
    def __init__(self, size, fixed=None, first=None):
        super().__init__(size, fixed)
        repeats = []
        for variable in range(7):
            readers = []
            for left,right,_ in self.nodes:
                selected = [port[variable] for port in (left,right) if variable<len(port)]
                reads = self.fresh()
                for selector in selected:
                    self.add(-selector,reads)
                self.add(-reads,*selected)
                readers.append(reads)
            repeat = self.fresh()
            repeats.append(repeat)
            for i,j in itertools.combinations(range(size),2):
                self.add(-readers[i],-readers[j],repeat)
            # repeat forces >=2 readers: omitting any one position leaves some reader.
            for i in range(size):
                self.add(-repeat,*(r for j,r in enumerate(readers) if i!=j))
            sensitive = [row for row in range(128) if not row & (1<<variable)
                         and base.target(row)!=base.target(row | (1<<variable))]
            assert 0 not in sensitive
            for i,(left,right,ops) in enumerate(self.nodes):
                # Each exclusive reader must itself distinguish all sensitive pairs.
                # Its output's direction for a fixed port follows directly from the
                # gate's truth table, so two unit-polarity restrictions suffice.
                for port,data in enumerate((left,right)):
                    if variable>=len(data):
                        continue
                    for op,operation in enumerate(ops):
                        positive = (op in (0,1) or (op==2 and port==0) or (op==3 and port==1))
                        for row in sensitive:
                            lo=self.values[i][row-1]
                            hi=self.values[i][(row | (1<<variable))-1]
                            guard=(repeat,-data[variable],-operation)
                            self.add(*guard,-lo if positive else lo)
                            self.add(*guard,hi if positive else -hi)
        if size<=10:
            # At ten binary nodes formula-only networks are already ruled out
            # by theta's cover number, mixed-leaf elimination and L-meta-517.
            # A shared binary gate costs one of the at most 4 fanout excesses.
            for four in itertools.combinations(repeats,4):
                self.add(*(-r for r in four))
        for left,right,_ in self.nodes:
            for a in range(min(7,len(left))):
                for b in range(a+1,7):
                    self.add(-left[a],-right[b],repeats[a])
                    self.add(-left[a],-right[b],repeats[b])
        if first is not None:
            left,right,_=self.nodes[0]
            self.add(left[first[0]])
            self.add(right[first[1]])


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--size',type=int,default=10)
    parser.add_argument('--write',type=Path)
    parser.add_argument('--decode',type=Path)
    parser.add_argument('--control',action='store_true')
    parser.add_argument('--first',nargs=2,type=int)
    args=parser.parse_args()
    base.selftest()
    e=Guarded(11 if args.control else args.size,base.control() if args.control else None,args.first)
    if args.write:e.write(args.write)
    if args.decode:e.decode(args.decode)
