/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.SLLVM.Cfg.Basic

/-! Transport for actual straight-line block prefixes. A prefix contains the
lifted expressions themselves, including memory operations. Renaming changes SSA operands; metadata differences additionally require a
kernel-checked equality of expression denotations. No arithmetic or memory
semantics is replaced. -/
namespace AgaveLatticeHash.MLIR
open LeanMLIR LeanMLIR.SLLVM

inductive BlockPrefix : Ctxt SLLVM.Ty → Ctxt SLLVM.Ty → Type
  | nil : BlockPrefix Γ Γ
  | var (e : Expr SLLVM Γ .impure ts) (p : BlockPrefix (ts ++ Γ) Δ) :
      BlockPrefix Γ Δ

namespace BlockPrefix

def denote : BlockPrefix Γ Δ → Γ.Valuation → EffectM Δ.Valuation
  | .nil, V => pure V
  | .var e p, V => e.denote V >>= p.denote

def append (p : BlockPrefix Γ Δ) (tail : BlockCom Δ Ω rets succs) :
    BlockCom Γ Ω rets succs :=
  match p with
  | .nil => tail
  | .var e p => .var e (p.append tail)

def toCom (p : BlockPrefix Γ Δ) (vs : HVector Δ.Var ts) : Com SLLVM Γ .impure ts :=
  match p with
  | .nil => .rets vs
  | .var e p => .var e (p.toCom vs)

/-- Inclusion of the incoming SSA context in the final context. -/
def contextHom (p : BlockPrefix Γ Δ) : Γ.Hom Δ :=
  match p with
  | .nil => .id
  | .var e p => fun _ v => p.contextHom (e.contextHom v)

/-- Even effectful instructions preserve all incoming SSA values. This law
lets a caller capture additional loop-carried values in its continuation. -/
theorem denote_preserves_context (p : BlockPrefix Γ Δ) (V : Γ.Valuation)
    (K : Δ.Valuation → Γ.Valuation → EffectM α) :
    (p.denote V >>= fun W => K W (W.comap p.contextHom)) =
      (p.denote V >>= fun W => K W V) := by
  induction p with
  | nil => rfl
  | var e p ih =>
    simp only [denote, bind_assoc]
    conv_lhs =>
      arg 2
      ext W
      rw [show (fun Z => K Z (Z.comap (contextHom (.var e p)))) =
          (fun Z => K Z ((Z.comap p.contextHom).comap e.contextHom)) from rfl]
      rw [ih W (fun Z U => K Z (U.comap e.contextHom))]
    simp [Expr.denote_unfold]

/-- A checkable certificate relating actual prefixes by an SSA variable map,
extended at every let. Any additional expression difference requires an
equality of denotations. The final map is explicit. -/
inductive Renamed : {Γ Δ Γ' Δ' : Ctxt SLLVM.Ty} → Γ.Hom Γ' →
    BlockPrefix Γ Δ → BlockPrefix Γ' Δ' → Δ.Hom Δ' → Prop
  | nil {Γ Γ' : Ctxt SLLVM.Ty} (f : Γ.Hom Γ') : Renamed f .nil .nil f
  | var {Γ Γ' Δ Δ' : Ctxt SLLVM.Ty} {f : Γ.Hom Γ'} {g : Δ.Hom Δ'} (e : Expr SLLVM Γ .impure ts)
      {p : BlockPrefix (ts ++ Γ) Δ} {q : BlockPrefix (ts ++ Γ') Δ'}
      (h : Renamed f.append p q g) :
      Renamed f (.var e p) (.var (e.changeVars f) q) g
  /-- Permit metadata differences only with an equality of the actual expression
  denotations and preservation of the syntactic purity classification. In
  particular, retained noalias scope names denote the same pure no-op. -/
  | var_semantic {Γ Γ' Δ Δ' : Ctxt SLLVM.Ty} {f : Γ.Hom Γ'} {g : Δ.Hom Δ'}
      (e : Expr SLLVM Γ .impure ts) (e' : Expr SLLVM Γ' .impure ts)
      {p : BlockPrefix (ts ++ Γ) Δ} {q : BlockPrefix (ts ++ Γ') Δ'}
      (he : e'.denote = (e.changeVars f).denote)
      (hPure : e.HasPureOp → e'.HasPureOp)
      (h : Renamed f.append p q g) :
      Renamed f (.var e p) (.var e' q) g

/-- Computational renaming, with its endpoint context and map. -/
structure Renaming (p : BlockPrefix Γ Δ) (f : Γ.Hom Γ') where
  out : Ctxt SLLVM.Ty
  body : BlockPrefix Γ' out
  map : Δ.Hom out
  certificate : Renamed f p body map

def changeVars (p : BlockPrefix Γ Δ) (f : Γ.Hom Γ') : Renaming p f :=
  match p with
  | .nil => ⟨Γ', .nil, f, .nil f⟩
  | .var e p =>
    let r := p.changeVars f.append
    ⟨r.out, .var (e.changeVars f) r.body, r.map, .var e r.certificate⟩

 theorem denote_append (p : BlockPrefix Γ Δ) (tail : BlockCom Δ Ω rets succs)
    (V : Γ.Valuation) :
    (p.append tail).denote V = p.denote V >>= tail.denote := by
  induction p with
  | nil => simp [append, denote]
  | var e p ih =>
    simp only [append, denote, BlockCom.denote_var, bind_assoc]
    congr 1
    funext W
    exact ih tail W

 theorem denote_toCom (p : BlockPrefix Γ Δ) (vs : HVector Δ.Var ts)
    (V : Γ.Valuation) :
    (p.toCom vs).denote V = (do
      let W ← p.denote V
      pure (vs.map W)) := by
  induction p with
  | nil => rfl
  | var e p ih =>
    simp only [toCom, denote, Com.denote_var, bind_assoc]
    congr 1
    funext W
    exact ih vs W

/-- Continuation transport for a renamed prefix, with no requirements on
instruction purity or on the continuation's effects. -/
 theorem Renamed.denote_bind {f : Γ.Hom Γ'} {g : Δ.Hom Δ'}
    {p : BlockPrefix Γ Δ} {q : BlockPrefix Γ' Δ'} (h : Renamed f p q g)
    (V : Γ'.Valuation) (K : Δ.Valuation → EffectM α) :
    (q.denote V >>= fun W => K (W.comap g)) = p.denote (V.comap f) >>= K := by
  induction h with
  | nil => rfl
  | var e h ih =>
    simp only [denote, bind_assoc]
    simp only [ih]
    simp [Expr.denote_unfold, Expr.denoteOp_changeVars]
  | var_semantic e e' he _hPure h ih =>
    simp only [denote, he, bind_assoc]
    simp only [ih]
    simp [Expr.denote_unfold, Expr.denoteOp_changeVars]

/-- Transport a continuation that also consumes untouched caller values.
This is the useful form when an inlined round carries extra batch-loop state. -/
theorem Renamed.denote_bind_with_context {f : Γ.Hom Γ'} {g : Δ.Hom Δ'}
    {p : BlockPrefix Γ Δ} {q : BlockPrefix Γ' Δ'} (h : Renamed f p q g)
    (V : Γ'.Valuation) (K : Δ.Valuation → Γ'.Valuation → EffectM α) :
    (q.denote V >>= fun W => K (W.comap g) (W.comap q.contextHom)) =
      (p.denote (V.comap f) >>= fun W => K W V) := by
  rw [q.denote_preserves_context V (fun W U => K (W.comap g) U)]
  exact h.denote_bind V (fun W => K W V)

 theorem Renamed.toCom_denote {f : Γ.Hom Γ'} {g : Δ.Hom Δ'}
    {p : BlockPrefix Γ Δ} {q : BlockPrefix Γ' Δ'} (h : Renamed f p q g)
    (V : Γ'.Valuation) (vs : HVector Δ.Var ts) :
    (q.toCom (vs.map g)).denote V = (p.toCom vs).denote (V.comap f) := by
  simp only [denote_toCom, HVector.map_map]
  exact h.denote_bind V (fun W => pure (vs.map W))

end BlockPrefix
end AgaveLatticeHash.MLIR
