import Datatypes 
import Signature (pfree)
import FreeCheck (checkTRS)
import Parser

import Data.Maybe (fromJust)

import Examples (flatten, flatten_fail, removePlus0_fail, skolemization, negativeNF, paper, non_linear)
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
  [ ("flatten", flatten),
    ("flatten_fail", flatten_fail),
    ("removePlus0_fail", removePlus0_fail),
    ("skolemization", skolemization),
    ("negativeNF", negativeNF),
    ("paper", paper),
    ("non_linear", non_linear)
  ]

parseResult :: Signature -> Map Rule [Term] -> String
parseResult sig map
  | null map  = "OK"
  | otherwise = foldlWithKey accuParse "Fail" map
  where accuParse s r ts = s ++ "\n\n" ++ show r ++ (concatMap (parseFail r) ts)
        parseFail r t = "\n" ++ show t ++ " is not " ++ show (getP r) ++ "-free"
        getP (Rule (Appl f _) _) = pfree sig f

run :: String -> String
run s =
  case parseModule "text area" s of
    Left err -> show err
    Right (Module sig trs) -> parseResult sig (checkTRS sig trs)

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
  Select.setValue exampleSelector "flatten"
  TextArea.setValue inputArea flatten
  return ()
