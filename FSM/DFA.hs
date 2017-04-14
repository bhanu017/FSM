module FSM.DFA where

    type DFA a = ([a], [Char], a->Char->[a], a, [a])

    initDFA :: a -> DFA a
    initDFA a = let delta _ _ = a:[] 
                in ([a], [], delta, a, [a])

    newState :: (Eq a) => DFA a -> a -> DFA a
    newState (q, sigma, delta, s, f) x = if (x `elem` q) then (q, sigma, delta, s, f) else (x:q , sigma, delta, s, f)

    markStart :: (Eq a) => DFA a -> a -> DFA a
    markStart (q, sigma, delta, s, f) x = if (x `elem` q) then (q, sigma, delta, x, f) else (q, sigma, delta, s, f)

    newTransition :: (Eq a) => DFA a -> ((a, Char), a) -> DFA a
    newTransition (q, sigma, delta, s, f) (( x, y), z) = let newsigma
                                                                | not(y `elem` sigma) = y:sigma
                                                                | otherwise = sigma
                                                             newdelta m n
                                                                | (m == x) && (n == y) && (x `elem` q) && (z `elem` q) && (not (z `elem` (delta x y))) = [z]
                                                                | otherwise                                                                            = delta m n
                                                         in (q, newsigma, newdelta, s, f)

    markFinal :: (Eq a) => DFA a -> a -> DFA a
    markFinal (q, sigma, delta, s, f) x = if (x `elem` q) && (not(x `elem` f)) then (q, sigma, delta, s, x:f) else (q, sigma, delta, s, f)

    states :: DFA a -> [a]
    states (q,_,_,_,_) = q

    finalStates :: DFA a -> [a]
    finalStates (_,_,_,_,f) = f

    transitions :: DFA a -> a -> Char -> [a]
    transitions (_,_, delta,_,_) = delta

    alphabet :: DFA a -> [Char]
    alphabet (_, sigma, _,_,_) = sigma 

    execDFA :: (Eq a) => DFA a -> [Char] -> Bool
    execDFA a@(q, sigma, delta, s, f) x = runDFA a s x

    runDFA :: (Eq a) => DFA a -> a -> [Char] -> Bool
    runDFA z@(q,sigma,delta,s,f) p (x:xs)   | (x:[] == []) && (p `elem` f) = True
                                            | (x:[] == []) && (not(p `elem` f)) = False
                                            | otherwise = runDFA z next xs
                                        where next = head (delta p x)

    givestlist:: (DFA a)->[a]->(DFA a)
    givestlist (q,sigma,delta,s,f) [] = (q,sigma,delta,s,f)
    givestlist (q,sigma,delta,s,f) ql = (ql,sigma,delta,head ql,f)

    giveflist:: (Eq a) => (DFA a)->[a]->(DFA a)
    giveflist (q,sigma,delta,s,f) fl = (q,sigma,delta,s,[fq | fq <- fl, fq `elem` q])

    givetlist:: (Eq a) => (DFA a)->[((a,Char),a)]->(DFA a)
    givetlist (q,sigma,delta,s,f) tl = foldr (flip newTransition) (q,sigma,let delta _ _ = [] in delta,s,f) tl
    
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


    --Initialise DFA
    --Add a new state
    --Add a new transition
    --