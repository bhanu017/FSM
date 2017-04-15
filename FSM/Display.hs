module Display where
    import DFA
    import NFA
    displayDFA :: (Show a) => (DFA a) -> IO()
    displayDFA (q, sigma, delta, s, f) = do
                                        putStr "<type>DFA</type>\n"
                                        prntstates q
                                        prntst s
                                        prntf f
                                        where prntstates x = if((length x) /= 0)
                                                             then
                                                                do
                                                                    --show x
                                                                    putStr "<state id=\""
                                                                    putStr $ (show(head x))
                                                                    putStr "\" name=\"q"
                                                                    putStr $ (show(head x))
                                                                    putStr "\">\n"
                                                                    putStr "<x>"
                                                                    putStr $ show(2)--xpos
                                                                    putStr "</x>\n<y>"
                                                                    putStr $ show(2)--ypos
                                                                    putStr "</y>\n</state>\n"
                                                                    prntstates (tail x)
                                                             else
                                                                do
                                                                    putStr ""

                                              prntst y = do
                                                            putStr "<start>"
                                                            putStr $ (show(y))
                                                            putStr "</start>\n"
                                              prntf z = if((length z) /= 0)
                                                        then
                                                            do
                                                                putStr "<final>"
                                                                putStr $ (show(head z))
                                                                putStr "</final>\n"
                                                                prntf (tail z)
                                                        else
                                                            do
                                                                putStr ""

    displayNFA :: (Show a) => (NFA a) -> IO()
    displayNFA (q, sigma, delta, s, f) = do
                                            putStr "<type>NFA</type>\n"
                                            prntstates q
                                            prntst s
                                            prntf f
                                            where prntstates x = if((length x) /= 0)
                                                                 then
                                                                    do
                                                                        --show x
                                                                        putStr "<state id=\""
                                                                        putStr $ (show(head x))
                                                                        putStr "\" name=\"q"
                                                                        putStr $ (show(head x))
                                                                        putStr "\">\n"
                                                                        putStr "<x>"
                                                                        putStr $ show(2)--xpos
                                                                        putStr "</x>\n<y>"
                                                                        putStr $ show(2)--ypos
                                                                        putStr "</y>\n</state>\n"
                                                                        prntstates (tail x)
                                                                 else
                                                                    do
                                                                        putStr ""

                                                  prntst y = do
                                                                putStr "<start>"
                                                                putStr $ (show(y))
                                                                putStr "</start>\n"
                                                  prntf z = if((length z) /= 0)
                                                            then
                                                                do
                                                                    putStr "<final>"
                                                                    putStr $ (show(head z))
                                                                    putStr "</final>\n"
                                                                    prntf (tail z)
                                                            else
                                                                do
                                                                    putStr ""

