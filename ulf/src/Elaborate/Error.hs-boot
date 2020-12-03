module Elaborate.Error where

import Common.Names

data ElabError

quantityError :: ElabError

reportM :: [Name] -> ElabError -> IO a


