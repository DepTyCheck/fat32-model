module Data.UniqFinVect.Derived

import public Data.UniqFinVect
import public Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Data.UniqFinVect.genUniqFinVect = deriveGen


