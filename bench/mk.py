import sys
rows=[l.split() for l in open('/tmp/vals.txt') if l.strip()]
ops={'addDown':(2,2),'mulUp':(3,2),'divDown':(4,2),'sqrtUp':(5,1),'subUp':(6,2)}
mod=sys.argv[1] if len(sys.argv)>1 else 'Interval64.Spec'
fn=sys.argv[2] if len(sys.argv)>2 else 'Spec.{op}'
for op,(col,ar) in ops.items():
    with open(f'bench/K_{op}.lean','w') as f:
        f.write(f"import Interval64\nopen Interval64 Interval64.Spec\n")
        seen=set()
        for r in rows:
            a,b=r[0],r[1]
            key=(a,b) if ar==2 else (a,)
            if key in seen: continue
            seen.add(key)
            call=f"{fn.format(op=op)} {a} {b}" if ar==2 else f"{fn.format(op=op)} {a}"
            f.write(f"example : ({call}).toNat = {r[col]} := by decide +kernel\n")
open('bench/K_base.lean','w').write("import Interval64\n")
