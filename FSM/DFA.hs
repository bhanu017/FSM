module FSM.DFA where

    type DFA a = ([a], [Char], a->Char->[a], a, [a])

    --Initialise DFA
    initDFA :: a -> DFA a
    initDFA a = let delta _ _ = a:[] 
                in ([a], [], delta, a, [a])

    --Add a new state
    newState :: (Eq a) => DFA a -> a -> DFA a
    newState (q, sigma, delta, s, f) x = if (x `elem` q) then (q, sigma, delta, s, f) else (x:q , sigma, delta, s, f)

    --mark the start state
    markStart :: (Eq a) => DFA a -> a -> DFA a
    markStart (q, sigma, delta, s, f) x = if (x `elem` q) then (q, sigma, delta, x, f) else (q, sigma, delta, s, f)

    --Add a new transition
    newTransition :: (Eq a) => DFA a -> ((a, Char), a) -> DFA a
    newTransition (q, sigma, delta, s, f) (( x, y), z) = let newsigma
                                                                | not(y `elem` sigma) = y:sigma
                                                                | otherwise = sigma
                                                             newdelta m n
                                                                | (m == x) && (n == y) && (x `elem` q) && (z `elem` q) && (not (z `elem` (delta x y))) = [z]
                                                                | otherwise                                                                            = delta m n
                                                         in (q, newsigma, newdelta, s, f)

    -- mark the final state
    markFinal :: (Eq a) => DFA a -> a -> DFA a
    markFinal (q, sigma, delta, s, f) x = if (x `elem` q) && (not(x `elem` f)) then (q, sigma, delta, s, x:f) else (q, sigma, delta, s, f)

    -- get the list of states
    states :: DFA a -> [a]
    states (q,_,_,_,_) = q

    -- get the list of final states
    finalStates :: DFA a -> [a]
    finalStates (_,_,_,_,f) = f

    -- get the list of transitions
    transitions :: DFA a -> a -> Char -> [a]
    transitions (_,_, delta,_,_) = delta

    -- get the list of input symbols
    alphabet :: DFA a -> [Char]
    alphabet (_, sigma, _,_,_) = sigma 

    -- execute the dfa on a string of symbols
    execDFA :: (Eq a) => DFA a -> [Char] -> Bool
    execDFA a@(q, sigma, delta, s, f) x = runDFA a s x

    -- run the dfa on a string
    runDFA :: (Eq a) => DFA a -> a -> [Char] -> Bool
    runDFA z@(q,sigma,delta,s,f) p (x:xs)   | (x:[] == []) && (p `elem` f) = True
                                            | (x:[] == []) && (not(p `elem` f)) = False
                                            | otherwise = runDFA z next xs
                                        where next = head (delta p x)

    -- set the list of states
    givestlist:: (DFA a)->[a]->(DFA a)
    givestlist (q,sigma,delta,s,f) [] = (q,sigma,delta,s,f)
    givestlist (q,sigma,delta,s,f) ql = (ql,sigma,delta,head ql,f)

    -- set the list of accept states
    giveflist:: (Eq a) => (DFA a)->[a]->(DFA a)
    giveflist (q,sigma,delta,s,f) fl = (q,sigma,delta,s,[fq | fq <- fl, fq `elem` q])

    -- set the list of transitions
    givetlist:: (Eq a) => (DFA a)->[((a,Char),a)]->(DFA a)
    givetlist (q,sigma,delta,s,f) tl = foldr (flip newTransition) (q,sigma,let delta _ _ = [] in delta,s,f) tl
    
    -- run the program.
    simulate:: (Eq a, Read a) => (DFA a)->IO ()
    simulate n = do
                        putStrLn "function? 1-givestlist, 2-giveflist, 3-givetlist, 4-exec, 5-exit"
                        choice <- getLine
                        if ((read choice::Int) == 1) then do
                                                            putStrLn "Give list of states:"
                                                            stlist <- getLine
                                                            simulate (givestlist n (read stlist))
                        else if ((read choice::Int) == 2) then do
                                                                putStrLn "Give list of final states:"
                                                                flist <- getLine
                                                                simulate (giveflist n (read flist))
                        else if ((read choice::Int) == 3) then do
                                                                putStrLn "Give list of transitions:"
                                                                tlist <- getLine
                                                                simulate (givetlist n (read tlist))
                        else if ((read choice::Int) == 4) then do
                                                                putStrLn "Enter String on which the DFA is run:"
                                                                str <- getLine
                                                                putStrLn (show (execDFA n (read str::String)))
                                                                simulate n
                        else                                 do 
                                                                putStrLn "DFA successfully simulated:"

-- Implementing the closure properties on DFAs

-- Union of two DFAs 
    unionDFA :: (Eq a, Eq b) => (DFA a) -> (DFA b) -> (DFA (a,b))
    unionDFA (q1, sigma1, delta1, s1, f1) (q2, sigma2, delta2, s2, f2) = 
        let newq = [(x, y) | x <- q1, y <- q2]
            newsigma = sigma1
            newdelta = (\ (x,y) ch -> [(head (delta1 x ch),head (delta2 y ch))])
            newstart = (s1, s2)
            newfinal = ([(x,y) | x <- f1, y <- q2] ++ [(x,y) | x <- q1, y <- f2])
        in (newq, newsigma, newdelta, newstart, newfinal)

-- intersection of two DFAs
    intersectionDFA :: (Eq a, Eq b) => (DFA a) -> (DFA b) -> (DFA (a,b))
    intersectionDFA (q1, sigma1, delta1, s1, f1) (q2, sigma2, delta2, s2, f2) =
        let newq = [(x, y) | x <- q1, y <- q2]
            newsigma = sigma1
            newdelta = (\ (x,y) ch -> [(head (delta1 x ch),head (delta2 y ch))])
            newstart = (s1, s2)
            newfinal = ([(x,y) | x <- f1, y <- f2])
        in (newq, newsigma, newdelta, newstart, newfinal)

--concatenation