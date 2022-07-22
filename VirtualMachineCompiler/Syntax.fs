module Syntax

open Utils

type Ty =
    | Int
    | Array of elemTy : Ty * numElems : int
    | Struct of List<VarDecl>
    | Ptr of ty : Ty
//  | TyId of string

    with

        static member IsEqual (tyA : Ty) (tyB : Ty) : bool =
            match (tyA, tyB) with
            | Int, Int ->
                true
            | Array(elemTyA, numElemsA), Array(elemTyB, numElemsB) ->
                (Ty.IsEqual elemTyA elemTyB) && numElemsA = numElemsB
            | Struct(varDeclsA), Struct(varDeclsB) ->
                let decEq (a : VarDecl) (b : VarDecl) =
                    (a.varName = b.varName) && (Ty.IsEqual a.ty b.ty)
                List.forall2 decEq varDeclsA varDeclsB
            | Ptr(tyA), Ptr(tyB) ->
                Ty.IsEqual tyA tyB
//          | TyId(idA), TyId(idB) ->
//              failwith "todo"
            | _, _ ->
                false

        member this.Size : int =
            match this with
            | Int ->
                1
            | Ptr(_) ->
                1
            | Array(elemTy, numElems) ->
                elemTy.Size * numElems
            | Struct(decls) ->
                List.sumBy (fun d -> d.ty.Size) decls
//            | TyId(name) ->
//                tyEnv[name].Size tyEnv

and TyEnv = Map<string, Ty>

and VarDecl = { 
    ty : Ty
    varName : string
}

type Expr = 
    | Plus of Expr * Expr * Range
    | Minus of Expr * Expr * Range
    | Times of Expr * Expr * Range
    | Eq of Expr * Expr * Range
    | Leq of Expr * Expr * Range
    | Geq of Expr * Expr * Range
    | Lt of Expr * Expr * Range
    | Assign of lTarget : Expr * rSource : Expr * Range
    | Var of string * Range
    | IntLiteral of int * Range
    | FunCall of funName : string * args : List<Expr> * Range

    with

        member this.Range =
            match this with
            | Plus(_,_,rng)
            | Minus(_,_,rng)
            | Times(_,_,rng)
            | Eq(_,_,rng)
            | Leq(_,_,rng)
            | Geq(_,_,rng)
            | Lt(_,_,rng)
            | Assign(_,_,rng)
            | IntLiteral(_,rng)
            | Var(_,rng)
            | FunCall(_,_,rng) ->
                rng

type SwitchCase = {
    scrutineeValue : int
    statement : Stat
}

and Stat =
    | ExprStat of Expr * Range
    | IfThen of cond : Expr * thenClause : Stat * Range
    | IfThenElse of cond : Expr * thenClause : Stat * elseClause : Stat * Range
    | While of cond : Expr * body : Stat * Range
    | For of init : Stat * cond : Expr * incr : Stat * body : Stat * Range
    | Switch of cond : Expr * cases : List<SwitchCase> * deflt : Stat * Range
    | Sequence of stat1 : Stat * stat2 : Stat * Range
    | Return of returnExpr : Expr * Range 
    | ReturnVoid of Range

type FunDecl = {
    name : string
    pars : List<VarDecl>
    retTy : Ty
    localDecls : List<VarDecl>
    body : Stat
}

type Prog = {
    globals : List<VarDecl>
    funDecls : List<FunDecl>
}