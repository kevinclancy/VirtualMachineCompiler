module Environment

open Syntax

type Address =
    | Local of offset : int
    | Global of absolute : int

type VarContextEntry = {
    address : Address
    ty : Ty
}

type FunContextEntry = {
    addr : int
    decl : FunDecl
}

type Context = {
    funCtxt : Map<string, FunContextEntry>
    varCtxt : Map<string, VarContextEntry>
    // number of words occupied by function arguments
    argumentSpace : int
    retAddr : int
    retTy : Ty
}
    with
        static member empty =
            { funCtxt = Map.empty ; varCtxt = Map.empty ; retAddr = 1 ; retTy = Int ; argumentSpace = 0 }

let rec elabGlobals (addrEnvInit : Context) (nextAddrInit : int) (decls : List<VarDecl>) : Context =
    let foldDecl ((ctxt, nextAddr) : Context * int) (decl : VarDecl) =
        { ctxt with varCtxt = ctxt.varCtxt.Add (decl.varName, { address = Global(nextAddr) ; ty = decl.ty }) }, (nextAddr + decl.ty.Size)
    fst <| List.fold foldDecl (addrEnvInit, nextAddrInit) decls

let rec elabLocals (addrEnvInit : Context) (nextAddrInit : int) (decls : List<VarDecl>) : Context =
    let foldDecl ((ctxt, nextAddr) : Context * int) (decl : VarDecl) =
        { ctxt with varCtxt = ctxt.varCtxt.Add (decl.varName, { address = Local(nextAddr) ; ty = decl.ty }) }, (nextAddr + decl.ty.Size)
    fst <| List.fold foldDecl (addrEnvInit, nextAddrInit) decls

let rec elabFormals (addrEnvInit : Context) (nextAddrInit : int) (decls : List<VarDecl>) : Context =
    let foldDecl ((ctxt, nextAddr) : Context * int) (decl : VarDecl) =
        { ctxt with varCtxt = ctxt.varCtxt.Add (decl.varName, { address = Local(nextAddr) ; ty = decl.ty }) }, (nextAddr - decl.ty.Size)
    fst <| List.fold foldDecl (addrEnvInit, nextAddrInit) decls

let envForFunc (ctxt : Context) (funAddr : int) (funDecl : FunDecl) : Context =
    let ctxt' = { ctxt with funCtxt = ctxt.funCtxt.Add (funDecl.name, { addr = funAddr ; decl = funDecl}) }
    let ctxt'' = elabFormals ctxt' -2 funDecl.pars
    elabLocals ctxt'' 1 funDecl.localDecls

    

