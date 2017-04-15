main :: IO ()

main = do
   initGUI
   window <- windowNew
   vbox <- vBoxNew False 0
   set window [containerBorderWidth := 10, 
               windowTitle := "Packing Demonstration",
               containerChild := vbox, windowDefaultWidth  := 550
             , windowDefaultHeight := 350 ]
   label1 <- labelNew (Just "hBoxNew False 0")
   miscSetAlignment label1 0 0
   boxPackStart vbox label1 PackNatural 0
   dbox <- hBoxNew False 0
   boxPackStart vbox dbox PackNatural 0
   dbutton <- buttonNewWithLabel "DFA"
   boxPackStart dbox dbutton PackNatural 0
   nbox <- hBoxNew False 0
   boxPackStart vbox nbox PackNatural 0
   nbutton <- buttonNewWithLabel "NFA"
   boxPackStart nbox nbutton PackNatural 0
   box1 <- makeBox False 0 PackNatural 0
   boxPackStart vbox box1 PackNatural 0
   onDestroy window mainQuit  
   widgetShowAll window
   mainGUI


makeBox :: Bool -> Int -> Packing -> Int -> IO HBox
makeBox homogeneous spacing packing padding = do
    box <- hBoxNew homogeneous spacing
    button1 <- buttonNewWithLabel "O"
    boxPackStart box button1 packing padding
    button2 <- buttonNewWithLabel "->"
    boxPackStart box button2 packing padding
    button3 <- buttonNewWithLabel "^"
    boxPackStart box button3 packing padding
    return box
