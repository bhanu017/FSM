{-NFA-}

module FSM.NFA where
        import Data.List
        type NFA a = ([a],[Char], a->(Maybe Char)->[a], a, [a]) --try to derive Show, Read
        -- empty language (base NFA)
        empty:: a->NFA a
        empty a = let delta a _ = [] in ([a],[],delta,a,[])

        markStart:: (Eq a) => (NFA a)->a->(NFA a)
        markStart (x,sig,del,s,f) y = if (y `elem` x) then (x,sig,del,y,f) else (x,sig,del,s,f)

        addState:: (Eq a) => (NFA a)->a->(NFA a)
        addState (x,sig,del,s,f) y = if (y `elem` x) then (x,sig,del,s,f) else (y:x,sig,del,s,f)

        addTransition:: (Eq a) => (NFA a)->a->(Maybe Char)->a->(NFA a)
        addTransition (x,sig,del,s,f) a Nothing c  = let newdel a Nothing
                                                       | (a `elem` x)&&(c `elem` x)&&(not (c `elem` (del a Nothing)))  = c:(del a Nothing)
                                                         newdel m n                                                    = del m n
                                                     in  (x,sig,newdel,s,f)
        addTransition (x,sig,del,s,f) a b c        = let newsig | ((maybe ' ' id b) `elem` sig) = sig
                                                                | otherwise                     = (maybe ' ' id b):sig
                                                         newdel a b
                                                                | (a `elem` x)&&(c `elem` x)&&(not (c `elem` (del a b))) = c:(del a b)
                                                         newdel m n                                                      = del m n
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

