{-NFA-}

module FSM.NFA where
        import Data.List
        type NFA a = ([a],[Char], a->(Maybe Char)->[a], a, [a]) --try to derive Show, Read
        -- empty language (base NFA)
        empty:: NFA ()
        empty = let delta _ _ = [] in ([()],[],delta,(),[])

        markStart:: (Eq a) => (NFA a)->a->(NFA a)
        markStart (x,sig,del,s,f) y = if (y `elem` x) then (x,sig,del,y,f) else (x,sig,del,s,f)

        addState:: (Eq a) => (NFA a)->a->(NFA a)
        addState (x,sig,del,s,f) y = if (y `elem` x) then (x,sig,del,s,f) else (y:x,sig,del,s,f)

        addTransition:: (Eq a) => (NFA a)->((a,(Maybe Char)),a)->(NFA a)
        addTransition (x,sig,del,s,f) ((a,Nothing),c)  = let newdel m n
                                                                    | (m == a)&&(n == Nothing)&&(a `elem` x)&&(c `elem` x)&&(not (c `elem` (del a Nothing)))  = c:(del a Nothing)
                                                                    | otherwise                                                                               = del m n
                                                         in  (x,sig,newdel,s,f)
        addTransition (x,sig,del,s,f) ((a,b),c)        = let newsig | ((maybe ' ' id b) `elem` sig) = sig
                                                                    | otherwise                     = (maybe ' ' id b):sig
                                                             newdel m n
                                                                    | (m == a)&&(n == b)&&(a `elem` x)&&(c `elem` x)&&(not (c `elem` (del a b))) = c:(del a b)
                                                                    | otherwise                                                                  = del m n
                                                         in  (x,newsig,newdel,s,f)

        markFinal:: (Eq a) => (NFA a)->a->(NFA a)
        markFinal (x,sig,del,s,f) a = if (a `elem` x)&&(not(a `elem` f)) then (x,sig,del,s,a:f) else (x,sig,del,s,f)


        runNFA:: (Eq a) => (NFA a)->[a]->[[Char]]->Bool
        runNFA z@(q,sig,del,s,f) [] []              = False    
        runNFA z@(q,sig,del,s,f) (x1:xs) ([]:ys)    | (x1 `elem` f) = True
                                                    | et /= []      = runNFA z (xs ++ et) (ys ++ take (length et) (repeat []))
                                                    | otherwise     = runNFA z (xs) (ys)
                                                    where
                                                      et            = del x1 Nothing
        runNFA z@(q,sig,del,s,f) (x1:xs) (y1:ys)    | (et /= [])&&(net /= [])           = runNFA z (xs ++ et ++ net) (ys ++ take (length et) (repeat y1) ++ take (length net) (repeat (tail y1)))
                                                    | (et == [])&&(net /= [])           = runNFA z (xs ++ net) (ys ++ take (length net) (repeat (tail y1)))
                                                    | (et /= [])&&(net == [])           = runNFA z (xs ++ et) (ys ++ take (length et) (repeat y1))
                                                    | otherwise                         = runNFA z (xs) (ys)

                                                    where
                                                      et  = del x1 Nothing
                                                      net = del x1 (Just (head y1)) 

        execNFA:: (Eq a) => (NFA a)->[Char]->Bool
        execNFA a@(q,sig,del,s,f) y = runNFA a [s] [y]

        st:: (NFA a)->[a]
        st (s,_,_,_,_) = s

        strst:: (NFA a)->a
        strst (_,_,_,s,_) = s

        finalst:: (NFA a)->[a]
        finalst (_,_,_,_,f) = f

        delta:: (NFA a)->(a->(Maybe Char)->[a])
        delta (_,_,del,_,_) = del

        sigma:: (NFA a)->[Char]
        sigma (_,sg,_,_,_) = sg

        givestlist:: (NFA a)->[a]->(NFA a)
        givestlist (q,sig,del,s,f) [] = (q,sig,del,s,f)
        givestlist (q,sig,del,s,f) ql = (ql,sig,del,head ql,f)

        giveflist:: (Eq a) => (NFA a)->[a]->(NFA a)
        --giveflist (q,sig,del,s,f) [] = (q,sig,del,s,f)
        giveflist (q,sig,del,s,f) fl = (q,sig,del,s,[fq | fq <- fl, fq `elem` q])

        givetlist:: (Eq a) => (NFA a)->[((a,(Maybe Char)),a)]->(NFA a)
        givetlist (q,sig,del,s,f) tl = foldr (flip addTransition) (q,sig,let delta _ _ = [] in delta,s,f) tl

        simulate:: (Eq a, Read a) => (NFA a)->IO ()
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
                                                                putStrLn "Enter String on which the NFA is run:"
                                                                str <- getLine
                                                                putStrLn (show (execNFA n (read str::String)))
                                                                simulate n
                        else                                 do 
                                                                putStrLn "NFA successfully simulated:"

        --Functions applied on two NFAs (for Closure Properties)
        concatNFA:: (Eq a, Eq b) => (NFA a)->(NFA b)->(NFA (Either a b))
        concatNFA (q1,sig1,del1,s1,f1) (q2,sig2,del2,s2,f2) = let nq               = [Left q | q<-q1] ++ [Right q | q<-q2]
                                                                  nsig             = nub (sig1 ++ sig2)
                                                                  ndel (Left m) n    | (m `elem` f1)&&(n == Nothing)  = (Right s2):[Left q | q <- (del1 m Nothing)]
                                                                                     | otherwise                      = [Left q | q <- (del1 m n)]
                                                                  ndel (Right m) n = [Right q | q <- (del2 m n)]
                                                                  ns               = Left s1
                                                                  nf               = [Right q | q <- f2]
                                                              in  (nq,nsig,ndel,ns,nf)

        unionNFA:: (Eq a, Eq b) => (NFA a)->(NFA b)->(NFA (Either () (Either a b)))
        unionNFA (q1,sig1,del1,s1,f1) (q2,sig2,del2,s2,f2)  = let ns                             = Left ()
                                                                  nq                             = (Left ()):[Right (Left q) | q<-q1] ++ [Right (Right q) | q<-q2]
                                                                  nsig                           = nub (sig1 ++ sig2)
                                                                  ndel (Left ()) Nothing         = [Right (Left s1), Right (Right s2)]
                                                                  ndel (Right (Left m)) n        = [Right (Left x) | x<-(del1 m n)]
                                                                  ndel (Right (Right m)) n       = [Right (Right x) | x<-(del2 m n)]
                                                                  ndel _ _                       = []
                                                                  nf                             = [Right (Left x) | x<-f1] ++ [Right (Right x) | x<-f2]
                                                              in  (nq,nsig,ndel,ns,nf)

        intersectNFA:: (Eq a, Eq b) => (NFA a)->(NFA b)->(NFA (a,b))
        intersectNFA (q1,sig1,del1,s1,f1) (q2,sig2,del2,s2,f2)    = let ns                                = (s1,s2)
                                                                        nq                                = [(q,r) | q<-q1, r<-q2]
                                                                        nsig                              = nub (sig1 ++ sig2)
                                                                        nf                                = [(q,r) | q<-f1, r<-f2]
                                                                        ndel (a,b) c                      = [(q,r) | q<-(del1 a c), r<-(del2 b c)]
                                                                    in  (nq,nsig,ndel,ns,nf)

        starNFA:: (Eq a) => (NFA a)->(NFA (Either () a))
        starNFA (q1,sig1,del1,s1,f1)                        = let ns                         = Left ()
                                                                  nq                         = (Left ()):[Right q | q<-q1]
                                                                  nsig                       = sig1
                                                                  nf                         = (Left ()):[Right q | q<-f1]
                                                                  ndel (Left ()) Nothing     = [Right s1]
                                                                  ndel (Right m) n           | (m `elem` f1)&&(n == Nothing)      = (Left ()):[Right q | q<-(del1 m Nothing)]
                                                                                             | otherwise                          = [Right q | q<-(del1 m n)]
                                                                  ndel _ _                   = []
                                                              in  (nq,nsig,ndel,ns,nf)

        








