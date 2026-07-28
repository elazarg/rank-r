import numpy as np, itertools
from math import comb
rng = np.random.default_rng(7)

def faces(r,m): return list(itertools.combinations(range(r),m))

def wedge_sign(j, L):
    """q_j ^ q_L = sign * q_sorted(L+{j});  sign = (-1)^{#{l in L : l < j}}."""
    if j in L: return 0, None
    s = (-1)**sum(1 for l in L if l < j)
    return s, tuple(sorted(L+(j,)))

def eta(I, e, r, k, idx):
    """(1/sqrt k) sum_t (-1)^{t-1} conj(e_{i_t}) (x) q_{I minus i_t}  in C^d (x) C^{C(r,k-1)}."""
    d = e.shape[0]; v = np.zeros((d, len(idx)), complex)
    for t, it in enumerate(I):
        J = tuple(x for x in I if x != it)
        v[:, idx[J]] += ((-1)**t) * np.conj(e[:, it])
    return v/np.sqrt(k)

def delta(L, e, r, k, idx):
    """(1/sqrt(r-k+2)) sum_{j notin L} e_j (x) (q_j ^ q_L)."""
    d = e.shape[0]; v = np.zeros((d, len(idx)), complex); n=0
    for j in range(r):
        s, J = wedge_sign(j, L)
        if s == 0: continue
        v[:, idx[J]] += s*e[:, j]; n += 1
    return v/np.sqrt(n)

def ip(x,y): return np.vdot(x.reshape(-1), y.reshape(-1))

for (d, r, k) in [(4,4,2),(4,4,3),(5,5,3),(5,6,4),(6,6,4),(4,5,5)]:
    if k > r: continue
    idx = {J:i for i,J in enumerate(faces(r,k-1))}
    # random orthonormal frame e_1..e_r in C^d needs r <= d; else use r <= d
    if r > d: continue
    e = np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))[0][:, :r]
    E = [eta(I,e,r,k,idx) for I in faces(r,k)]
    gram = np.array([[ip(a,b) for b in E] for a in E])
    orth = np.linalg.norm(gram - np.eye(len(E)))
    # symmetric Kraus operator
    B = rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)); A = B + B.T
    D = [delta(L,e,r,k,idx) for L in faces(r,k-2)] if k>=2 else []
    worst = 0.0
    for I in faces(r,k):
        AI = A @ eta(I,e,r,k,idx)          # (A (x) id) eta_I
        for dl in D:
            worst = max(worst, abs(ip(dl, AI)))
    # control: a NON-symmetric A should not be orthogonal
    A2 = rng.normal(size=(d,d))+1j*rng.normal(size=(d,d))
    ctrl = max(abs(ip(dl, A2 @ eta(I,e,r,k,idx))) for I in faces(r,k) for dl in D) if D else float('nan')
    print(f"d={d} r={r} k={k}: |Gram-I|={orth:.2e}  dim protected={len(D)} (=C({r},{k-2})={comb(r,k-2)})  "
          f"max|<delta_L,(A(x)id)eta_I>| sym={worst:.2e}  nonsym={ctrl:.3f}")

print("\n=== operator inequality:  (Phi (x) id)(P_H)  <=  d_up * beta_k * (I - Pi) ===")
def beta_k(As, k, restarts=30, iters=400):
    d = As[0].shape[0]
    best = 0.0
    for _ in range(restarts):
        X = rng.normal(size=(d,k))+1j*rng.normal(size=(d,k))
        Y = rng.normal(size=(d,k))+1j*rng.normal(size=(d,k))
        for _ in range(iters):
            M = X@Y.conj().T; n = np.linalg.norm(M,'fro')
            if n < 1e-12: break
            M = M/n
            G = sum(np.vdot(A,M)*A for A in As)      # gradient of sum_a |<A,M>|^2
            U,s,Vh = np.linalg.svd(G)
            X = U[:,:k]*s[:k]; Y = Vh[:k,:].conj().T
        M = X@Y.conj().T; M = M/np.linalg.norm(M,'fro')
        best = max(best, sum(abs(np.vdot(A,M))**2 for A in As))
    return best/k

for (d,r,k,nA) in [(4,4,2,3),(4,4,3,3),(5,5,3,4),(6,6,4,3)]:
    idx = {J:i for i,J in enumerate(faces(r,k-1))}; F = len(idx)
    e = np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))[0][:, :r]
    As = []
    for _ in range(nA):
        B = rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)); As.append(B+B.T)
    bk = beta_k(As,k); dup = r-k+1
    P = np.zeros((d*F,d*F),complex)
    for I in faces(r,k):
        v = eta(I,e,r,k,idx)
        for A in As:
            w = (A@v).reshape(-1); P += np.outer(w, w.conj())
    D = np.array([delta(L,e,r,k,idx).reshape(-1) for L in faces(r,k-2)])
    Q,_ = np.linalg.qr(D.T); Pi = Q@Q.conj().T
    lam_plain = np.linalg.eigvalsh(P - dup*bk*np.eye(d*F))[-1]
    lam_sharp = np.linalg.eigvalsh(P - dup*bk*(np.eye(d*F)-Pi))[-1]
    print(f"d={d} r={r} k={k}: beta_k={bk:.4f} d_up={dup}  "
          f"lam_max(P - d*b*I)={lam_plain:+.3e}   lam_max(P - d*b*(I-Pi))={lam_sharp:+.3e}")
