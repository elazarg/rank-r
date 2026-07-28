import numpy as np
rng = np.random.default_rng(1)

def so_basis(d):
    B=[]
    for a in range(d):
        for b in range(a+1,d):
            L=np.zeros((d,d),complex); L[a,b]=1; L[b,a]=-1; B.append(L/np.sqrt(2))
    return B

def proj_basis(dU,dV):
    """Frobenius-orthonormal basis of so(U) (x) so(V)."""
    T=[np.kron(L,M) for L in so_basis(dU) for M in so_basis(dV)]
    return [T_/np.linalg.norm(T_,'fro') for T_ in T]

def kappa(dU,dV,k,restarts=60,iters=800):
    """kappa_k = max{ ||Pi_A(M)||_F^2 : rank M <= k, ||M||_F = 1 }  (Johnston-Kribs duality)."""
    T=proj_basis(dU,dV); n=dU*dV
    if not T: return None
    def Pi(M): return sum(np.vdot(Ti,M)*Ti for Ti in T)
    best=0.0
    for _ in range(restarts):
        A=rng.normal(size=(n,k))+1j*rng.normal(size=(n,k))
        B=rng.normal(size=(n,k))+1j*rng.normal(size=(n,k))
        for _ in range(iters):
            M=A@B.conj().T; nf=np.linalg.norm(M,'fro')
            if nf<1e-12: break
            M=M/nf
            G=Pi(M)                      # gradient of ||Pi M||_F^2 is 2 Pi M
            U,s,Vh=np.linalg.svd(G)      # best rank-k approx of the gradient
            A=U[:,:k]*s[:k]; B=Vh[:k,:].conj().T
        M=A@B.conj().T; M=M/np.linalg.norm(M,'fro')
        best=max(best,float(np.linalg.norm(Pi(M),'fro')**2))
    return best

for (dU,dV) in [(2,2),(3,2),(3,3),(4,3),(4,4)]:
    row=[]
    for k in [1,2,3,4]:
        v=kappa(dU,dV,k)
        row.append("--" if v is None else f"{v:.5f}")
    print(f"so({dU})(x)so({dV}):  k=1 {row[0]}   k=2 {row[1]}   k=3 {row[2]}   k=4 {row[3]}")
print()
print("claimed kappa_k = min(k,4)/4 :  0.25000   0.50000   0.75000   1.00000")
