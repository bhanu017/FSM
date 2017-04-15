{-NFA-}

module NFA where
        import Data.List
        import DFA
        
        type NFA a = ([a],[Char], a->(Maybe Char)->[a], a, [a]) --try to derive Show, Read Not possible
        
        type PartNFA a = ([a],[[Char]],a->[Char]->[a],a,[a])
        
        -- init NFA (base NFA)
        
        initNFA:: a -> (NFA a)
        initNFA a = let delta _ _ = [] in ([a],[],delta,a,[a])

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

        
        deltaset::(Show a) => (NFA a)->IO ()
        deltaset z@(q1,sig1,del1,s1,f1) = do
                                            putStrLn "set of Transitions between states:\n"
                                            prnt set
                                          where set      = [(q,Just c,r) | q<-q1, c<-sig1, r<-(del1 q (Just c))] ++ [(q,Nothing,r) | q<-q1, r<-(del1 q Nothing)]
                                                prnt x   = if ((length x) == 0)
                                                           then
                                                              do putStrLn "Done!\n"
                                                           else
                                                              do
                                                                 putStrLn ((show (head x)) ++ ",\n")
                                                                 prnt (tail x)

        
        givestlist:: (NFA a)->[a]->(NFA a)
        givestlist (q,sig,del,s,f) [] = (q,sig,del,s,f)
        givestlist (q,sig,del,s,f) ql = (ql,sig,del,head ql,f)

       
        giveflist:: (Eq a) => (NFA a)->[a]->(NFA a)
        --giveflist (q,sig,del,s,f) [] = (q,sig,del,s,f)
        giveflist (q,sig,del,s,f) fl = (q,sig,del,s,[fq | fq <- fl, fq `elem` q])

        
        givetlist:: (Eq a) => (NFA a)->[((a,(Maybe Char)),a)]->(NFA a)
        givetlist (q,sig,del,s,f) tl = foldr (flip addTransition) (q,sig,let delta _ _ = [] in delta,s,f) tl


        displayNFA :: (Show a) => (NFA a) -> IO()
        displayNFA (q, sigma, delta1, s, f) = do
                                            putStr "< NFA >\n"
                                            --prntstates q
                                            putStr "< Transtions >"
                                            prntdelta del
                                            putStr "\n< Start State >"
                                            putStr $ (show(s))
                                            putStr "\n< Accept states >"
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
                                                  del = [((j,k),l) | j <- q, k <- sigma, l <- (delta1 j (Just k))] ++ [((j,'?'),l) | j <- q, l <- (delta1 j Nothing)]
                                                  prntdelta w = if((length w) /= 0)
                                                                then
                                                                    do
                                                                        putStr "<from> "
                                                                        putStr $ (show(fst(fst(head w))))
                                                                        putStr "\t<read> "
                                                                        putStr(show(snd(fst(head w))))
                                                                        putStr "\t<to> "
                                                                        putStr $ (show(snd(head w)))
                                                                        putStr "\n"
                                                                        prntdelta (tail w)
                                                                else
                                                                    do
                                                                        putStr ""

        
        simulateNFA:: (Eq a, Read a, Show a) => (NFA a)->IO ()
        
        simulateNFA n = do
                        putStrLn "function? 1-givestlist, 2-giveflist, 3-givetlist, 4-display, 5-exec, 6-exit"
                        choice <- getLine
                        if ((read choice::Int) == 1) then do
                                                            putStrLn "Give list of states:"
                                                            stlist <- getLine
                                                            simulateNFA (givestlist n (read stlist))
                        else if ((read choice::Int) == 2) then do
                                                                putStrLn "Give list of final states:"
                                                                flist <- getLine
                                                                simulateNFA (giveflist n (read flist))
                        else if ((read choice::Int) == 3) then do
                                                                putStrLn "Give list of transitions:"
                                                                tlist <- getLine
                                                                simulateNFA (givetlist n (read tlist))
                        else if ((read choice::Int) == 4) then do 
                                                                displayNFA n
                                                                simulateNFA n
                        else if ((read choice::Int) == 5) then do
                                                                putStrLn "Enter String on which the NFA is run:"
                                                                str <- getLine
                                                                putStrLn (show (execNFA n (read str::String)))
                                                                simulateNFA n
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

        
        formNFAfromPartial:: (Eq a) => (PartNFA a)-> (NFA [a])
        
        formNFAfromPartial (q1,sig1,del1,s1,f1)             = let ns                         = [s1]
                                                                  nq                         = [[q] | q<-q1]
                                                                  nsig                       = sig1
                                                                  nf                         = [[q] | q<-f1]
                                                                  ndel [m] n                 = [[q] | q<-(del1 m n)]
                                                              in  helperfNfP (nq,nsig,ndel,ns,nf) []

        
        helperfNfP:: (Eq a) => (PartNFA [a])-> [Char] -> (NFA [a])
        
        helperfNfp z@(q1,[],del1,s1,f1) sig2                  = let del2 m Nothing            = [q | q<-(del1 m "")]
                                                                    del2 m (Just n)           = [q | q<-(del1 m [n])]
                                                                in  (q1,sig2,del2,s1,f1)

        helperfNfP z@(q1,x:sig1,del1,s1,f1) sig2              | (length x == 0) = helperfNfP (q1,sig1,del1,s1,f1) sig2
                                                              | (length x == 1) = helperfNfP (q1,sig1,del1,s1,f1) (nub(sig2 ++ x))
                                                              | otherwise       = let left          = [q | q<-q1, (del1 q x) /= []]
                                                                                      right         = nub (foldr (++) [] [(del1 q x) | q<-q1])
                                                                                      newstate      = (head left) ++ (head right)
                                                                                      nq            = newstate:q1
                                                                                      nsig2         = if ((head x) `elem` sig2) then sig2 else (head x):sig2
                                                                                      nsig1         = (tail x):sig1
                                                                                      ndel m n      | (n == x)                                       = []
                                                                                                    | (m `elem` left)&&(n == [head x])               = [newstate]
                                                                                                    | (m == newstate)&&(n == (tail x))               = right
                                                                                                    | otherwise                                      = del1 m n
                                                                                  in  helperfNfP (nq,nsig1,ndel,s1,f1) nsig2

        
        formIntNFAfromPartial:: (PartNFA Int)-> (NFA Int)
        
        formIntNFAfromPartial (q1,sig1,del1,s1,f1)          = let ns                         = s1
                                                                  nq                         = q1
                                                                  nsig                       = sig1
                                                                  nf                         = f1
                                                                  ndel m n                   = del1 m n
                                                              in  helperfIntNfP (nq,nsig,ndel,ns,nf) [] (foldr (max) 0 q1)

        
        helperfIntNfP:: (PartNFA Int)-> [Char] ->Int-> (NFA Int)

        helperfIntNfp z@(q1,[],del1,s1,f1) sig2 ns            = let del2 m Nothing            = [q | q<-(del1 m "")]
                                                                    del2 m (Just n)           = [q | q<-(del1 m [n])]
                                                                in  (q1,sig2,del2,s1,f1)

        helperfIntNfP z@(q1,x:sig1,del1,s1,f1) sig2 ns        | (length x == 0) = let nsig2 = sig2
                                                                                      nns   = ns
                                                                                  in  helperfIntNfP (q1,sig1,del1,s1,f1) nsig2 nns
                                                              | (length x == 1) = let nsig2 = (nub(sig2 ++ x))
                                                                                      nns   = ns
                                                                                  in  helperfIntNfP (q1,sig1,del1,s1,f1) nsig2 nns
                                                              | otherwise       = let left          = [q | q<-q1, (del1 q x) /= []]
                                                                                      right         = nub (foldr (++) [] [(del1 q x) | q<-q1])
                                                                                      newstate      = (ns + 1)
                                                                                      nq            = newstate:q1
                                                                                      nsig2         = if ((head x) `elem` sig2) then sig2 else (head x):sig2
                                                                                      nsig1         = (tail x):sig1
                                                                                      ndel m n      | (n == x)                                       = []
                                                                                                    | (m `elem` left)&&(n == [head x])               = [newstate]
                                                                                                    | (m == newstate)&&(n == (tail x))               = right
                                                                                                    | otherwise                                      = del1 m n
                                                                                  in  helperfIntNfP (nq,nsig1,ndel,s1,f1) nsig2 newstate


        convertENFAtoNFA:: (Eq a) => (NFA a)->(DFA a)

        convertENFAtoNFA z@(q1,sig1,del1,s1,f1)       = let stack = [q | q<-q1, (q /= s1), (del1 q Nothing) /= []]
                                                        in  helpereNtN z stack


        helpereNtN:: (Eq a) => (NFA a)->[a]->(DFA a)

        helpereNtN z@(q1,sig1,del1,s1,f1) []          = let nq          = q1
                                                            nsig        = sig1
                                                            nf          | (length [q | q<-(del1 s1 Nothing), (q `elem` f1)] /= 0)   = nub(s1:f1)
                                                                        | otherwise                                                 = f1
                                                            ndel m n    | (m == s1)&&((del1 m Nothing) /= [])    = nub ((del1 m (Just n)) ++ (foldr (++) [] [(del1 q (Just n)) | q <- (del1 m Nothing)]))
                                                                        | otherwise                              = (del1 m (Just n))
                                                            ns          = s1
                                                        in  (nq, nsig, ndel, ns, nf)

        helpereNtN z@(q1,sig1,del1,s1,f1) (x:xs)      = let to                  = del1 x Nothing
                                                            from1               = [(q, Just c) | q<-q1, c<-sig1, (x `elem` (del1 q (Just c)))]
                                                            from2               = [(q, Nothing) | q<-q1, (x `elem` (del1 q Nothing))]
                                                            newdel m n          | (m == x)&&(n == Nothing)   = []
                                                                                | ((m, n) `elem` from1)      = nub((del1 m n) ++ to)
                                                                                | ((m,n) `elem` from2)       = nub((del1 m n) ++ to)
                                                                                | otherwise                  = (del1 m n)
                                                        in  helpereNtN (q1,sig1,newdel,s1,f1) xs


        convertNFAtoDFA:: (Eq a) => (DFA a)->(DFA [a])

        convertNFAtoDFA (q1,sig1,del1,s1,f1)        = let del2 m n = []
                                                          stack    = [[s1]]
                                                      in  helperNFAtoDFA (q1,sig1,del1,s1,f1) [[s1]] del2 [s1] stack


        helperNFAtoDFA:: (Eq a) => (DFA a)->[[a]]->([a]->Char->[[a]])->[a]->[[a]]->(DFA [a])

        helperNFAtoDFA  z@(q1,sig1,del1,s1,f1) q2 del2 s2 []        = let ns             = s2
                                                                          nf             = nub([q | q<-q2, r<-q, (r `elem` f1)])
                                                                          ndel           = del2
                                                                          nq             = q2
                                                                          nsig           = sig1
                                                                      in  (nq,nsig,ndel,ns,nf)

        helperNFAtoDFA  z@(q1,sig1,del1,s1,f1) q2 del2 s2 (s:sx)    = let newstates      = [(nub(foldr (++) [] [(del1 q ch) | q<-s]),ch) | ch<-sig1]
                                                                          newstack       = nub (sx ++ [q | (q,r)<-newstates, not (q `elem` q2)])
                                                                          newq           = nub (q2 ++ [q | (q,r)<-newstates])
                                                                          newdel m n     | (m==s)&&(n `elem` sig1)    =  [fst (newstates !!(maybe 0 id(elemIndex n [r | (q,r)<-newstates])))]
                                                                                         | otherwise                  =  del2 m n
                                                                      in  helperNFAtoDFA z newq newdel s2 newstack


        convertENFAtoDFA:: (Eq a) => (NFA a)->(DFA [a])

        convertENFAtoDFA z            = convertNFAtoDFA (convertENFAtoNFA z)
{- END -}









        












