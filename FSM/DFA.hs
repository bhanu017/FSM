module DFA where

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
																| (m == x) && (n == y) && (x `elem` q) && (z `elem` q) && (not (z `elem` (delta x y))) = z : delta x y
																| otherwise																			   = delta m n
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
	runDFA z@(q,sigma,delta,s,f) p (x:xs)	| (x:[] == []) && (p `elem` f) = True
											| (x:[] == []) && (not(p `elem` f)) = False
											| otherwise = runDFA z next xs
										where next = head (delta p x) 
	--Initialise DFA
	--Add a new state
	--Add a new transition
	--