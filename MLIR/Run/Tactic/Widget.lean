module

public meta import Lean.Elab.Tactic
public meta import ProofWidgets.Data.Html
public meta import ProofWidgets.Component.Panel.Basic
public meta import ProofWidgets.Component.OfRpcMethod
public meta import MLIR.Run.Tactic.Parse

/-! An infoview panel showing the instruction the next step runs, and the one after it. -/

namespace MLIR.Tactic

open Lean Meta Server ProofWidgets Jsx

public meta section

/-- Up to `n` instructions of `block` from `idx` on, and whether the exit comes within them. -/
def upcomingInstrs (block idx : Expr) (n : Nat) : MetaM (Array Expr × Bool) := do
  let mut rest ← bodyFrom block idx
  let mut out := #[]
  while out.size < n && rest.isAppOfArity ``List.cons 3 do
    out := out.push rest.appFn!.appArg!
    rest ← whnfD rest.appArg!
  return (out, rest.isAppOfArity ``List.nil 1)

/-- The current and next instructions of the `runBodyFrom` in `goal`; nothing without one. -/
def instrsHtml (goal : Expr) : MetaM Html := do
  let .ok r ← (getRunBodyFrom? goal).run | return .text ""
  let (instrs, exit) ← upcomingInstrs r.block r.idx 2
  let idx := (← whnfD r.idx).nat?
  let row (label : String) (e : Expr) : MetaM Html := do
    return <tr><td
              className="pr2">{.text
                  label}</td><td><InteractiveCode fmt={← Widget.ppExprTagged e}/></td></tr>
  let mut rows := #[]
  for h : k in [0:instrs.size] do
    let label :=
      match idx with
      | some i => s!"[{i + k}]"
      | none => if k == 0 then "current" else "next"
    rows := rows.push (← row label instrs[k])
  if exit then
    rows := rows.push (← row "exit" (← whnfD (← mkAppM ``BasicBlock.exit #[r.block])))
  return <details
        «open»={true}><summary
            className="mv2 pointer">Instructions</summary><table
            className="ml1 font-code">{...rows}</table></details>

@[server_rpc_method]
def Instrs.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let some g := props.goals[0]? | return .text ""
    g.ctx.val.runMetaM {} do
        let md ← g.mvarId.getDecl
        let lctx := md.lctx |>.sanitizeNames.run' { options := (← getOptions) }
        withLCtx lctx md.localInstances do
            instrsHtml (← instantiateMVars md.type)

/-- The current and next instructions, in the infoview, for any goal about a block's body. -/
@[widget_module]
def Instrs : Component PanelWidgetProps :=
  mk_rpc_widget%Instrs.rpc

/-- `Instrs` with no props, as `show_panel_widgets [Instrs]` would build it. The command defines
this instance non-`meta`, which a module cannot do for a `meta` widget. -/
def Instrs.instance : Widget.WidgetInstance where
  id := ``Instrs
  javascriptHash := (Widget.ToModule.toModule Instrs).javascriptHash
  props := Server.RpcEncodable.rpcEncode (Json.mkObj [])

end

-- `show_panel_widgets [Instrs]`: shown in every importing file
run_cmd
  Widget.addPanelWidgetGlobal (Widget.ToModule.toModule Instrs).javascriptHash ``Instrs.instance

end MLIR.Tactic
