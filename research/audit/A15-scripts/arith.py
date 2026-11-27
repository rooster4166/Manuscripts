# Brute-force checks of every budget inequality used in spine.tex
fl=lambda a: a//2  # floor(a/2) for a>=0
import math
ok=True
def chk(c,msg):
    global ok
    if not c: ok=False; print("FAIL",msg)
R=range(0,40)
# Lemma 4.3 cut, Case 1: x in S, r_i unmarked counts, n-|S|=r1+r2
for r1 in R:
  for r2 in R:
    tgt=fl(r1+r2)
    if r1%2 and r2%2: chk((r1-1)//2+(r2-1)//2+1<=tgt,("1a",r1,r2))
    if r1%2==0:
      # (1b) q(G1+,S1)<= floor((r1+1)/2)=r1/2
      chk(fl(r1+1)==r1//2,("1b-plus",r1))
      chk(r1//2-1+fl(r2)+1<=tgt and r1//2+fl(r2)<=tgt,("1b",r1,r2))
    # Case 2: x not in S, n-|S|=r1+r2+1
    tgt2=fl(r1+r2+1)
    if r1%2: chk(fl(r1)+fl(r2)+1<=tgt2,("2a",r1,r2))
    if r1%2==0 and r2%2==0:
      chk(fl(r1+1)==r1//2,"2b-a"); chk(r1//2+r2//2<=tgt2,("2b",r1,r2))
      chk((r1//2+1)+r2//2-1<=tgt2,("2c",r1,r2))
# Leaf lemma cases: n>=3, s=|S|
for n in range(3,40):
  for s in range(1,n+1):
    t=fl(n-s)
    chk(fl((n-1)-(s-1))<=t,"L1/L3")
    if s==1: chk(fl(n-2)<=fl(n-1),"L2")
    if s==1 and n%2: chk(fl(n-2)+1<=fl(n-1),"L4")
    if s+1<=n-1: chk(fl(n-1-s-1)+1<=t,("L5",n,s))
  chk(fl(n-3)+1<=fl(n-1),"double leaf")
  if n%2==0 and n>=4:
    k=(n-2)//2; chk(fl(2*k)==k and fl(n-1)==k,"pendant")
# Theorem 4.11 final inequality: floor((n+a)/2)-a-ceil(o/2) <= floor((n-a-o)/2)
for n in range(1,60):
  for a in range(0,n+1):
    for o in range(0,n-a+1):
      lhs=fl(n+a)-a+fl(o)-o
      chk(lhs==fl(n-a)-(o+1)//2,"4.11 eq")
      chk(lhs<=fl(n-a-o),("4.11",n,a,o))
# Lemma 4.10 count: floor((X+AX-t)/2)+floor((Y+AY-t)/2)+t <= floor((n+a)/2)
for X in range(1,15):
 for Y in range(1,15):
  for AX in range(0,X+1):
   for AY in range(0,Y+1):
    for t in range(1,min(X,Y)+1):
      chk(fl(X+AX-t)+fl(Y+AY-t)+t<=fl(X+Y+AX+AY),"lemma6 count")
# Cone step: n-t odd, t>=2
for n in range(3,60):
  for t in range(2,n+1):
    if (n-t)%2:
      if n%2==0: chk(t%2==1,"parity"); D=(n+1)//2+1; chk(2*D-3-t<=n-1-t,"cone even")  # t+2q<=2D-3
      else: chk(t%2==0,"parity"); D=(n+1)//2; chk(2*D-2<=n-1,"cone odd")
      chk((n-1-t)//2==fl(n-t),"cone floor")
  # singletons
  if n%2==0: chk(n//2-1==fl(n-1),"sing even")
  else: chk((n-3)//2+1==fl(n-1) and fl(n-2)==(n-3)//2,"sing odd")
  for s in range(2,n+1):
    if (n-s)%2==0:
      sp=s-1
      if sp>=2: chk((n-sp-1)//2==(n-s)//2,"general cone")
      else: chk(n%2==0 and (n-2)//2==(n-s)//2,"general single")
# Lemma 6.3
for N in range(1,60):
  if N%2==0: chk(fl(N-1)==N//2-1,"6.3a") 
  else:
    chk(fl(N)+1==(N+1)//2,"6.3b")
    if N>=3: chk(fl(N-2)==(N-3)//2 and (N-3)//2+1==(N-1)//2==fl(N),"6.3c")
# Root analysis: |U|=n-2s
for n in range(3,60):
  for s in range(1,n//2+1):
    U=n-2*s
    if U<1: continue
    if n%2==0: chk(U//2+s==n//2,"R1 lift")
    else: chk(fl(U)+1+s==fl(n)+1 and fl(U)+s==fl(n),"R2 lift")
# Tests and converse budgets
for n in range(3,60):
  if n%2==1: chk((n+1-1)//2==n//2 if False else True,"")
for n in range(3,60): # B order n, J order n+1
  if n%2==0: chk((n+1-1)//2==n//2,"T1 budget")
  else: chk((n+1)//2==fl(n)+1,"T2 budget")
for N in range(1,60): chk(fl(N-1)+1==(N+1)//2,"gallai")
# bridge double: 2p<=N+1 -> p<=N/2 for N even
for N in range(2,60,2): chk(fl(N+1)==N//2,"bridge")
# separator: odd |C|=2s+1: |U|=n-(2s+1)+1=n-2s ; even |C|=2s: n-2s
print("ALL OK" if ok else "FAILURES")
