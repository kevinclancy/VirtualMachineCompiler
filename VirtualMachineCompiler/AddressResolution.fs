module AddressResolution

open TargetCode

let resolve (instructions : List<Instruction>) : Instruction [] =
    let mutable restInstructions = instructions
    // stores the result of resolving addresses in the *instructions* input
    let mutable result = ResizeArray()
    // maps symbolic addresses to absolute addresses
    let mutable addrMap : Map<int, int> = Map.empty

    while not (List.isEmpty restInstructions) do
        match restInstructions.Head with
        | SymbolicAddress(addr) ->
            addrMap <- addrMap.Add(addr, result.Count)
        | instr ->
            result.Add instr
        restInstructions <- restInstructions.Tail

    for i in 0 .. (result.Count - 1) do
        result[i] <-
            match result[i] with
            | Jump addr ->
                Jump addrMap[addr]
            | JumpZ addr ->
                JumpZ addrMap[addr]
            | JumpI addr ->
                JumpI addrMap[addr]
            | LoadCAddr addr ->
                LoadC addrMap[addr]
            | _ ->
                result[i]

    result.ToArray()