module DFA where
    import Data.List
    

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
    givestlistDFA:: (DFA a)->[a]->(DFA a)
    givestlistDFA (q,sigma,delta,s,f) [] = (q,sigma,delta,s,f)
    givestlistDFA (q,sigma,delta,s,f) ql = (ql,sigma,delta,head ql,f)

    -- set the list of accept states
    giveflistDFA:: (Eq a) => (DFA a)->[a]->(DFA a)
    giveflistDFA (q,sigma,delta,s,f) fl = (q,sigma,delta,s,[fq | fq <- fl, fq `elem` q])

    -- set the list of transitions
    givetlistDFA:: (Eq a) => (DFA a)->[((a,Char),a)]->(DFA a)
    givetlistDFA (q,sigma,delta,s,f) tl = foldr (flip newTransition) (q,sigma,let delta _ _ = [] in delta,s,f) tl


    displayDFA :: (Show a) => (DFA a) -> IO()
    displayDFA (q, sigma, delta, s, f) = do
                                        putStr "< DFA >\n"
                                        --putStr "< States > "
                                        --prntstates q
                                        putStr "< Transtions >\n"
                                        prnttrans del
                                        putStr "\n< Start State >\t = "
                                        putStr $ show(s)
                                        putStr "\n< Accept States >\t = "
                                        prntf f
                                        where prntf z = if((length z) /= 0)
                                                        then
                                                            do
                                                                putStr $ (show(head z))
                                                                putStr "\t"
                                                                prntf (tail z)
                                                        else
                                                            do
                                                                putStr ""
                                              del = [((j, k) ,l) | j <- q, k <- sigma, l <- delta j k]
                                              prnttrans w = if((length w) /= 0)
                                                            then
                                                                do
                                                                    putStr "<from> "
                                                                    putStr $ (show(fst(fst(head w))))
                                                                    putStr "\t"
                                                                    putStr "<read> "
                                                                    putStr $ (show(snd(fst(head w))))
                                                                    putStr "\t"
                                                                    putStr "<to> "
                                                                    putStr $ (show(snd(head w)))
                                                                    putStr "\t"
                                                                    putStr "\n"
                                                                    prnttrans (tail w)
                                                            else
                                                                do
                                                                    putStr ""
    
    -- run the program.
    simulateDFA:: (Eq a, Read a, Show a) => (DFA a)->IO ()
    simulateDFA n = do
                        putStrLn "function? 1-givestlistDFA, 2-giveflistDFA, 3-givetlistDFA, 4-display, 5-exec, 6-exit"
                        choice <- getLine
                        if ((read choice::Int) == 1) then do
                                                            putStrLn "Give list of states:"
                                                            stlist <- getLine
                                                            simulateDFA (givestlistDFA n (read stlist))
                        else if ((read choice::Int) == 2) then do
                                                                putStrLn "Give list of final states:"
                                                                flist <- getLine
                                                                simulateDFA (giveflistDFA n (read flist))
                        else if ((read choice::Int) == 3) then do
                                                                putStrLn "Give list of transitions:"
                                                                tlist <- getLine
                                                                simulateDFA (givetlistDFA n (read tlist))
                        else if ((read choice::Int) == 4) then do
                                                                displayDFA n
                                                                simulateDFA n
                        else if ((read choice::Int) == 5) then do
                                                                putStrLn "Enter String on which the DFA is run:"
                                                                str <- getLine
                                                                putStrLn (show (execDFA n (read str::String)))
                                                                simulateDFA n
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
--    concatNFA:: (Eq a, Eq b) => (DFA a)->(DFA b)->(NFA (Either a b))
--    concatNFA (q1,sig1,del1,s1,f1) (q2,sig2,del2,s2,f2) = let nq = [Left q | q<-q1] ++ [Right q | q<-q2]
--                                                              nsig = nub (sig1 ++ sig2)
--                                                              ndel (Left m) n | (m `elem` f1) && (n == Nothing) = (Right s2):[Left q | q <- (del1 m Nothing)]
  --                                                                            | otherwise = [Left q | q <- (del1 m n)]
    --                                                          ndel (Right m) n = [Right q | q <- (del2 m n)]
      --                                                        ns               = Left s1
        --                                                      nf               = [Right q | q <- f2]
          --                                                in  (nq,nsig,ndel,ns,nf)
