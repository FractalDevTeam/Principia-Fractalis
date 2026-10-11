# PF homogeneous DE cosmology derived from ch08 action (isotropic FRW, Pontryagin ch2=0).
# Exponential quintessence V=V0 exp(-lambda phi), lambda=1/sqrt(8pi (M/MPl)^2). See
# codex/COSMOLOGY_DE_DERIVATION_2026-10-11.md. Reduced units MPl,red=kappa=H0=1, Om_m0=0.315.
import numpy as np
from scipy.integrate import solve_ivp
Om_m0=0.315; Om_phi0=0.685; rho_m0=3*Om_m0
def run(lmbda,V0,a_i=1e-2,t_max=10.0):
    def H(a,phi,pd): return np.sqrt(max(rho_m0*a**-3+0.5*pd*pd+V0*np.exp(-lmbda*phi),1e-30)/3.0)
    def rhs(t,y):
        a,phi,pd=y; Hh=H(a,phi,pd); V=V0*np.exp(-lmbda*phi)
        return [a*Hh,pd,-3*Hh*pd+lmbda*V]
    ev=lambda t,y:y[0]-1.0; ev.terminal=True; ev.direction=1
    return solve_ivp(rhs,[0,t_max],[a_i,0,0],events=ev,rtol=1e-9,atol=1e-12,max_step=1e-2)
def Omphi(lmbda,V0):
    s=run(lmbda,V0)
    if not len(s.t_events[0]): return None
    a,phi,pd=s.y[:,-1]; V=V0*np.exp(-lmbda*phi); rp=0.5*pd*pd+V
    return rp/(rp+rho_m0*a**-3)
def tune(lmbda):
    lo,hi=1e-3,10.0
    for _ in range(80):
        m=0.5*(lo+hi); O=Omphi(lmbda,m)
        if O is None or O<Om_phi0: lo=m
        else: hi=m
    return 0.5*(lo+hi)
if __name__=="__main__":
    for M in [0.287,0.4,0.6,1.0]:
        lm=1/np.sqrt(8*np.pi*M*M); V0=tune(lm); s=run(lm,V0)
        a,phi,pd=s.y; V=V0*np.exp(-lm*phi); K=0.5*pd*pd; w=(K-V)/(K+V)
        msk=a>=0.25; A=np.vstack([np.ones(msk.sum()),1-a[msk]]).T
        w0,wa=np.linalg.lstsq(A,w[msk],rcond=None)[0]
        print(f"M={M} lam={lm:.3f} w*={-1+lm*lm/3:.3f} w0={w0:.3f} wa={wa:.3f} wmin={w.min():.4f}")
