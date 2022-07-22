module VirtualMachine

open TargetCode

let maxDataMem = 10000

let execute (code : Instruction []) : int =
    let mutable PC = 0
    let mutable SP = 0
    let mutable EP = 1
    let mutable HP = maxDataMem
    let mutable FP = 1
    let mutable mem = Array.create maxDataMem 0

    // executes the next instruction
    // return - false if the instruction was HALT, and true otherwise
    let step () : bool =
        match code[PC] with
        | Halt ->
            false
        | Mul ->
            mem[SP - 1] <- mem[SP - 1] * mem[SP]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Add ->
            mem[SP - 1] <- mem[SP - 1] + mem[SP]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Sub ->
            mem[SP - 1] <- mem[SP - 1] - mem[SP]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Leq ->
            mem[SP - 1] <- if mem[SP - 1] <= mem[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Eq ->
            mem[SP - 1] <- if mem[SP - 1] = mem[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Geq ->
            mem[SP - 1] <- if mem[SP - 1] >= mem[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Lt ->
            mem[SP - 1] <- if mem[SP - 1] < mem[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Neg ->
            mem[SP] <- -mem[SP]
            PC <- PC + 1
            true
        | Pop ->
            SP <- SP - 1
            PC <- PC + 1
            true
        | Dup ->
            mem[SP + 1] <- mem[SP]
            SP <- SP + 1
            PC <- PC + 1
            true
        | LoadC(constantToLoad) ->
            SP <- SP + 1
            mem[SP] <- constantToLoad
            PC <- PC + 1
            true
        | Load(numWordsToLoad) ->
            for i in (numWordsToLoad - 1) .. -1 .. 0 do
                mem[SP + i] <- mem[mem[SP] + i]
            SP <- SP + numWordsToLoad - 1
            PC <- PC + 1
            true
        | Store(numWordsToStore) ->
            for i in 0 .. (numWordsToStore - 1) do
                mem[mem[SP] + i] <- mem[SP - numWordsToStore + i]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Jump(dest) ->
            PC <- dest
            true
        | JumpZ(dest) ->
            PC <- if mem[SP] = 0 then dest else (PC + 1)
            SP <- SP - 1
            true
        | JumpI(jumpOffset) ->
            PC <- mem[SP] + jumpOffset
            SP <- SP - 1
            true
        | New ->
            match HP - mem[SP] > EP with
            | true ->
                HP <- HP - mem[SP]
                mem[SP] <- HP
            | false ->
                mem[SP] <- 0
            PC <- PC + 1
            true
        | LoadRC(frameOffset) ->
            SP <- SP + 1
            mem[SP] <- FP + frameOffset
            PC <- PC + 1
            true
        | LoadR(loadFromFPOffset, numWordsToLoad) ->
            SP <- SP + 1
            let addrToLoadFrom = mem[FP + loadFromFPOffset]
            for i in (numWordsToLoad - 1) .. -1 .. 0 do
                mem[SP + i] <- mem[addrToLoadFrom + i]
            SP <- SP + numWordsToLoad - 1
            PC <- PC + 1
            true
        | StoreR(destOffset, numWordsToStore) ->
            let destAddr = mem[FP + destOffset]
            for i in 0 .. (numWordsToStore - 1) do
                mem[destAddr + i] <- mem[SP - numWordsToStore + i]
            PC <- PC + 1
            true
        | Mark ->
            mem[SP + 1] <- EP
            mem[SP + 2] <- FP
            SP <- SP + 2
            PC <- PC + 1
            true
        | Call ->
            FP <- SP
            let tmp = PC
            PC <- mem[SP]
            mem[SP] <- tmp
            true
        | Slide(slideDistance, numWordsToSlide) ->
            match slideDistance with
            | 0 ->
                true
            | _ ->
                if numWordsToSlide = 0 then 
                    SP <- SP - slideDistance
                else
                    SP <- SP - slideDistance - numWordsToSlide
                    for _ in 0 .. (numWordsToSlide - 1) do
                        SP <- SP + 1
                        mem[SP] <- mem[SP + slideDistance]
                true
        | Alloc(numWords) ->
            SP <- SP + numWords
            true
        | Enter(maxFrameSize) ->
            EP <- SP + maxFrameSize
            if EP >= HP then failwith "Stack overflow" else ()
            PC <- PC + 1
            true
        | Return(wordsToRemove) ->
            PC <- mem[FP]
            EP <- mem[FP - 2]
            if EP >= HP then failwith "Stack overflow" else ()
            SP <- FP - wordsToRemove
            FP <- mem[FP - 1]
            true
        | SymbolicAddress(_) ->
            failwith "symbolic addresses must be resolved before code execution"

    while step() do
        ()

    mem[1]