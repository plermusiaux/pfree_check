import Datatypes 
import FreeCheck
import Parser

import Data.Maybe (fromJust)

import Examples (flatten1, flatten_fail, flatten2, negativeNF,
                 removePlus0_fail, removePlus0, skolemization,
                 non_linear,
                 delete, insertionSort, mergeSort, multiply0,
                 reverse, reverseTwice)

import Control.Monad.IO.Class ()
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

import Data.Map (Map, foldlWithKey)
import Data.List (concatMap)

examples =
  [ ("flatten1", flatten1),
    ("flatten_fail", flatten_fail),
    ("flatten2", flatten2),
    ("negativeNF", negativeNF),
    ("removePlus0_fail", removePlus0_fail),
    ("removePlus0", removePlus0),
    ("skolemization", skolemization),
    ("non_linear", non_linear),
    ("delete", delete),
    ("insertionSort", insertionSort),
    ("mergeSort", mergeSort),
    ("multiply0", multiply0),
    ("reverse", Examples.reverse),
    ("reverseTwice", reverseTwice)
  ]

parseResult :: Signature -> Map Rule (Term,[Term]) -> String
parseResult sig map
  | null map  = "OK"
  | otherwise = foldlWithKey accuParse "Fail" map
  where accuParse s r (p,ts) = s ++ "\n\n" ++ show r ++ (concatMap (parseFail r p) ts)
        parseFail r p t = "\n" ++ show t ++ " is not " ++ show p ++ "-free"

run :: String -> String
run s =
  case parseModule "text area" s of
    Left err -> show err
    Right (Module sig trs) -> parseResult sig (checkTRS Default sig trs)

main = do
  doc <- currentDocumentUnchecked
  inputArea <-
    unsafeCastTo HTMLTextAreaElement =<< getElementByIdUnsafe doc "input-area"
  outputArea <- getElementByIdUnsafe doc "output-area"
  checkButton <-
    unsafeCastTo HTMLButtonElement =<<
    getElementByIdUnsafe doc "check-button"
  exampleSelector <-
    unsafeCastTo HTMLSelectElement =<<
    getElementByIdUnsafe doc "example-selector"
  on checkButton click $
    do inputText <- TextArea.getValue inputArea
       setInnerHTML outputArea (run inputText)
       return ()
  on exampleSelector change $
    do name <- Select.getValue exampleSelector
       TextArea.setValue inputArea (fromJust (lookup name examples))
  Select.setValue exampleSelector "flatten1"
  TextArea.setValue inputArea flatten1
  return ()
