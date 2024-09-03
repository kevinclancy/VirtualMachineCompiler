module Environment

open Syntax

type Address =
    /// A local addresses that is relative to the framepointer: its absolute address is FP+offset
    | Local of offset : int
    /// An absolute address
    | Global of absolute : int

type VarContextEntry = {
    /// The address of the variable in data memory
    address : Address
    /// The type of the variable
    ty : Ty
}

type FunContextEntry = {
    /// The symbolic address of the function entry point
    addr : int
    /// The function declaration
    decl : FunDecl
}

type Context = {
    /// Maps each function name in context to information about the function
    funCtxt : Map<string, FunContextEntry>
    /// Maps each variable name in context to information about the variable
    varCtxt : Map<string, VarContextEntry>
    /// Number of words occupied by current function arguments
    argumentSpace : int
    /// The address to place the current function's return value at
    retAddr : int
    /// The current function's return type
    retTy : Ty
}
    with
        static member empty =
            { funCtxt = Map.empty ; varCtxt = Map.empty ; retAddr = 1 ; retTy = Int ; argumentSpace = 0 }

/// Return an extended version of `ctxtInit`, where each global variable declared in `decls` has been assigned a memory address
///
/// ## Parameters
///
/// * ctxtInit - The context to extend
/// * nextAddrInit - The next available memory address to use for a global variable
/// * decls - The declarations of global variables to extend `ctxtInit` with
///
/// ## Returns
///
/// * The result of extending `ctxtInit` with all of the global variable declarations in `decls`
let rec elabGlobals (ctxtInit : Context) (nextAddrInit : int) (decls : List<VarDecl>) : Context =
    let foldDecl ((ctxt, nextAddr) : Context * int) (decl : VarDecl) =
        { ctxt with varCtxt = ctxt.varCtxt.Add (decl.varName, { address = Global(nextAddr) ; ty = decl.ty }) }, (nextAddr + decl.ty.Size)
    fst <| List.fold foldDecl (ctxtInit, nextAddrInit) decls

/// Return an extended version of `ctxtInit`, where each local variable declared in `decls` has been assigned a memory address
///
/// ## Parameters
///
/// * ctxtInit - The context to extend
/// * nextAddrInit - The next available memory address to use for a local variable
/// * decls - The declarations of local variables to extend `ctxtInit` with
///
/// ## Returns
///
/// * The result of extending `ctxtInit` with all of the local variable declarations in `decls`
let rec elabLocals (ctxtInit : Context) (nextAddrInit : int) (decls : List<VarDecl>) : Context =
    let foldDecl ((ctxt, nextAddr) : Context * int) (decl : VarDecl) =
        { ctxt with varCtxt = ctxt.varCtxt.Add (decl.varName, { address = Local(nextAddr) ; ty = decl.ty }) }, (nextAddr + decl.ty.Size)
    fst <| List.fold foldDecl (ctxtInit, nextAddrInit) decls

/// Return an extended version of `ctxtInit`, where each formal argument declared in `decls` has been assigned a memory address
///
/// ## Parameters
///
/// * ctxtInit - The context to extend
/// * nextAddrInit - The next available memory address to use for an argument
/// * decls - The declarations of formal arguments to extend `ctxtInit` with
///
/// ## Returns
///
/// * The result of extending `ctxtInit` with all of the formal argument declarations in `decls`
let rec elabFormals (addrCtxtInit : Context) (nextAddrInit : int) (decls : List<VarDecl>) : Context =
    let foldDecl ((ctxt, nextAddr) : Context * int) (decl : VarDecl) =
        { ctxt with varCtxt = ctxt.varCtxt.Add (decl.varName, { address = Local(nextAddr) ; ty = decl.ty }) }, (nextAddr - decl.ty.Size)
    fst <| List.fold foldDecl (addrCtxtInit, nextAddrInit) decls

/// Extended `ctxt` with the function declared by `funDecl` at symbolic address `funAddr`
///
/// ## Parameters
///
/// * ctxt - the context to extend with a new function
/// * funAddr - the symbolic address of the function's first instruction
/// * funDecl - the declaration of the function
///
/// ## Returns
///
/// * `ctxt` extended with the function declared by `funDecl`
let ctxtForFunc (ctxt : Context) (funAddr : int) (funDecl : FunDecl) : Context =
    let ctxt' = {
        ctxt with
            funCtxt = ctxt.funCtxt.Add (funDecl.name, { addr = funAddr ; decl = funDecl})
    }
    let ctxt'' = elabFormals ctxt' -3 funDecl.pars
    elabLocals ctxt'' 1 funDecl.localDecls



