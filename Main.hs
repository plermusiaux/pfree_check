import Control.Monad.IO.Class ( liftIO )
import Control.Concurrent.MVar ()
import GHCJS.DOM (currentDocumentUnchecked)
import GHCJS.DOM.Types
       (HTMLTextAreaElement(HTMLTextAreaElement),
        HTMLSelectElement(HTMLSelectElement),
        HTMLButtonElement(HTMLButtonElement), Element(Element),
        unsafeCastTo)
import GHCJS.DOM.Document ()
import GHCJS.DOM.Element (setInnerHTML)
import GHCJS.DOM.Node ()
import GHCJS.DOM.EventM (on)
import GHCJS.DOM.GlobalEventHandlers (click, change)
import GHCJS.DOM.NonElementParentNode (getElementByIdUnsafe)
import qualified GHCJS.DOM.HTMLTextAreaElement as TextArea
       (setValue, getValue)
import qualified GHCJS.DOM.HTMLSelectElement as Select (setValue, getValue)


import Data.List (concatMap)
import Data.Map (Map, foldlWithKey)
import Data.Maybe (fromJust)


import Datatypes 
import FreeCheck
import Parser

import Examples

examples =
  [ ("flatten1", flatten1),
    ("flatten_fail", flatten_fail),
    ("flatten2", flatten2),
    ("flatten3", flatten3),
    ("negativeNF", negativeNF),
    ("skolemization", skolemization),
    ("removePlus0_fail", removePlus0_fail),
    ("removePlus0", removePlus0),
    ("multiply0", multiply0),
    ("non_linear", non_linear),
    ("insertionSort", insertionSort),
    ("mergeSort", mergeSort),
    ("reverse", Examples.reverse),
    ("reverseTwice", reverseTwice),
    ("delete", delete),
    ("sortedDelete", sortedDelete),
    ("otrs", otrs)
  ]

parseResult :: Signature -> Map Rule (Term,[Term]) -> String
parseResult sig map
  | null map  = "OK"
  | otherwise = foldlWithKey accuParse "Fail" map
  where accuParse s r (p,ts) = s ++ "\n\n" ++ show r ++ (concatMap (parseFail r p) ts)
        parseFail r p t = "\n" ++ show t ++ " is not " ++ show p ++ "-free"

run :: Flag -> String -> IO String
run flag s =
  case parseModule "text area" s of
    Left err -> return $ show err
    Right (Module sig trs) -> parseResult sig <$> checkTRS flag sig trs

main = do
  doc <- currentDocumentUnchecked
  inputArea <-
    unsafeCastTo HTMLTextAreaElement =<< getElementByIdUnsafe doc "input-area"
  outputArea <- getElementByIdUnsafe doc "output-area"
  checkButton <-
    unsafeCastTo HTMLButtonElement =<<
    getElementByIdUnsafe doc "check-button"
  checkLinearButton <-
    unsafeCastTo HTMLButtonElement =<<
    getElementByIdUnsafe doc "check-linear-button"
  checkStrictButton <-
    unsafeCastTo HTMLButtonElement =<<
    getElementByIdUnsafe doc "check-strict-button"
  exampleSelector <-
    unsafeCastTo HTMLSelectElement =<<
    getElementByIdUnsafe doc "example-selector"
  on checkButton click $
    do inputText <- TextArea.getValue inputArea
       outputText <- liftIO $ run Default inputText
       setInnerHTML outputArea outputText
  on checkLinearButton click $
    do inputText <- TextArea.getValue inputArea
       outputText <- liftIO $ run Linearized inputText
       setInnerHTML outputArea outputText
  on checkStrictButton click $
    do inputText <- TextArea.getValue inputArea
       outputText <- liftIO $ run Strict inputText
       setInnerHTML outputArea outputText
  on exampleSelector change $
    do name <- Select.getValue exampleSelector
       TextArea.setValue inputArea (fromJust (lookup name examples))
  Select.setValue exampleSelector "flatten1"
  TextArea.setValue inputArea flatten1
