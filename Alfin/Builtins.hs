module Alfin.Builtins where

import Alfin.AsmLang
import Alfin.LowCore

data FunKind
  = RealFun ShapeType
  | FixFun ShapeType
  | PrimFun String
  | SelFun QName Int  -- ConName, index
  | IdFun
  | PrimOp ShapeType
  | CmpFun
  | ErrFun Int
  deriving (Show, Eq)

baseData :: [DataDef]
baseData =
  [DataDef ("GHCziTypes","Int") [(("GHCziTypes","Izh"), [PType "Int"])]
  ,DataDef ("GHCziTypes","Char") [(("GHCziTypes","Czh"), [PType "Char"])]
  ,DataDef ("GHCziBool","Bool") [(("GHCziBool","False"), []), (("GHCziBool","True"), [])]
  ,DataDef ("GHCziTypes","ZC") [(("GHCziTypes","ZMZN"), []), (("GHCziTypes","ZC"), [RefType, RefType])]
  ,DataDef ("GHCziPrim", "Z2H") [(("GHCziPrim", "Z2H"), [RefType, RefType])]  -- unboxed 2 tuple -- FIXME does unboxed matter for us??
  ,DataDef ("","ErrorCode") [(("","ErrorCode"), [PType "Int"])]
  ,DataDef ("Flite", "List") [(("Flite","Nil"), []), (("Flite","Cons"), [RefType, RefType])]
  ,DataDef ("Flite", "Maybe") [(("Flite","Nothing"), []), (("Flite","Just"), [RefType])]
  ,DataDef ("Flite", "Ordering") [(("Flite","LT"), []), (("Flite","EQ"), []), (("Flite","GT"), [])]
  ,DataDef ("Flite", "Pair") [(("Flite","Pair"), [RefType, RefType])]
  ,DataDef ("", "(#2#)") [(("", "(#2#)"), [RefType, RefType])]
  ,DataDef ("", "(#3#)") [(("", "(#3#)"), [RefType, RefType, RefType])]
  ]

defaultPrimBox :: String -> CName
defaultPrimBox "Int" = CName "GHCziTypes.Izh"

boxConstrs :: [QName]
boxConstrs =
  [("GHCziTypes","Izh")
  ]

isUnboxTupleCon :: QName -> Bool
isUnboxTupleCon ("GHCziPrim", ('Z':_:'H':[])) = True
isUnboxTupleCon _                             = False

baseFuns :: [(QName, ([ShapeType], FunKind))]
baseFuns =
  [(("GHCziPrim","zlzh"), ([PType "Int", PType "Int"], CmpFun))
  ,(("GHCziPrim","zlzezh"), ([PType "Int", PType "Int"], CmpFun))
  ,(("GHCziPrim","zgzh"), ([PType "Int", PType "Int"], CmpFun))
  ,(("GHCziPrim","zszezh"), ([PType "Int", PType "Int"], CmpFun))
  ,(("GHCziPrim","zezezh"), ([PType "Int", PType "Int"], CmpFun))
  ,(("GHCziPrim","zgzezh"), ([PType "Int", PType "Int"], CmpFun))
  ,(("GHCziPrim","zmzh"), ([PType "Int", PType "Int"], PrimOp (PType "Int")))
  ,(("GHCziPrim","zpzh"), ([PType "Int", PType "Int"], PrimOp (PType "Int")))
  ,(("GHCziPrim","ztzh"), ([PType "Int", PType "Int"], PrimOp (PType "Int")))
  ,(("GHCziPrim","negateIntzh"), ([PType "Int"], PrimOp (PType "Int")))
  ,(("GHCziBase","modIntzh"), ([PType "Int", PType "Int"], PrimOp (PType "Int")))
-- workaround to support some error throwing functions
  ,(("GHCziErr","overflowError"), ([], ErrFun 1))
  ,(("GHCziErr","divZZeroError"), ([], ErrFun 2))
  ,(("ControlziExceptionziBase","patError"), ([RefType], ErrFun 3))
  ,(("GHCziList","badHead"), ([], ErrFun 4))
  ]

compareFuns :: [QName]
compareFuns = map fst $ filter ((==CmpFun) . snd . snd) baseFuns

boxIntTag :: AsmTag
boxIntTag = BoxCon (CName "GHCziTypes.Izh")

boxIntResult :: String -> (CallResultRef, Maybe (AsmTag, [Parameter], FetchHint))
boxIntResult x = (dummyResultRef, Just (boxIntTag, [pp x], Nothing))

builtinPrimOps :: [((QName, ([ShapeType], FunKind)), Function)]
builtinPrimOps =
  [((("GHCziBase","unpackCStringzh"), ([RefType], RealFun RefType)),
    Function (FName "GHCziBase.unpackCStringzh") Nothing (Just 0) [rp "x"] (AsmBlock [] (TailCall (EvalRef (rv "x")) [])))
  ,((("Flite","str"), ([RefType], RealFun RefType)),
    Function (FName "Flite.str") Nothing (Just 0) [rp "ys"] (AsmBlock [] (CaseOf (EvalRef (rv "ys")) [] (dummyResultRef) Nothing
    [((CName "GHCziTypes.ZMZN"), [], Nothing, AsmBlock [] (NodeReturn (ConTag (CName "Flite.Nil")) []))
    ,((CName "GHCziTypes.ZC"), [rp "x", rp "xs"], Nothing, AsmBlock 
      [(dummyResultRef, Just (BoxCon (CName "GHCziTypes.Czh"), [pp "c"], Nothing)) :<=: (EvalRef (rv "x"), [])
      ,"z" :<-: StoreNode (boxIntTag) [pa "c"]
      ,"zs" :<-: StoreNode (FunTag $ FName "Flite.str") [ra "xs"]
      ] (NodeReturn (ConTag (CName "Flite.Cons")) [ra "z", ra "zs"]))
    ])))
  ,((("Flite","emit"), ([RefType, RefType], RealFun RefType)),
   Function (FName "Flite.emit") Nothing (Just 0) [rp "i", rp "k"] (AsmBlock
     [boxIntResult "x" :<=: (EvalRef (rv "i"), [])
     ,Put_IO (ConTag (CName "GHCziTypes.Czh")) [pa "x"]]
     (TailCall (EvalRef (rv "k")) [])
    ))
  ,((("GHCziBase","plusInt"), ([RefType, RefType], RealFun RefType)),
    Function (FName "GHCziBase.plusInt") Nothing (Just 0) [rp "a", rp "b"] (AsmBlock
      [boxIntResult "x" :<=: (EvalRef (rv "a"), [])
      ,boxIntResult "y" :<=: (EvalRef (rv "b"), [])
      ,"z" :<~: RunPrimOp (OpName "zpzh") (pv "x") (Just $ pv "y")]
      (NodeReturn boxIntTag [pa "z"]))
    )
  ,((("GHCziBase","minusInt"), ([RefType, RefType], RealFun RefType)),
    Function (FName "GHCziBase.minusInt") Nothing (Just 0) [rp "a", rp "b"] (AsmBlock
      [boxIntResult "x" :<=: (EvalRef (rv "a"), [])
      ,boxIntResult "y" :<=: (EvalRef (rv "b"), [])
      ,"z" :<~: RunPrimOp (OpName "zmzh") (pv "x") (Just $ pv "y")]
      (NodeReturn boxIntTag [pa "z"]))
    )
  ,((("GHCziBase","timesInt"), ([RefType, RefType], RealFun RefType)),
    Function (FName "GHCziBase.timesInt") Nothing (Just 0) [rp "a", rp "b"] (AsmBlock
      [boxIntResult "x" :<=: (EvalRef (rv "a"), [])
      ,boxIntResult "y" :<=: (EvalRef (rv "b"), [])
      ,"z" :<~: RunPrimOp (OpName "ztzh") (pv "x") (Just $ pv "y")]
      (NodeReturn boxIntTag [pa "z"]))
    )
  ,((("GHCziBase","eqInt"), ([RefType, RefType], RealFun RefType)),
    Function (FName "GHCziBase.eqInt") Nothing (Just 0) [rp "a", rp "b"] (AsmBlock
      [boxIntResult "x" :<=: (EvalRef (rv "a"), [])
      ,boxIntResult "y" :<=: (EvalRef (rv "b"), [])
      ,"z" :<-?: RunCmpOp (OpName "zezezh") (pv "x") (pv "y")]
      (BoolReturn "z" (ConTag (CName "GHCziBool.True")) (ConTag (CName "GHCziBool.False"))))
    )
  ,((("GHCziBase","neInt"), ([RefType, RefType], RealFun RefType)),
    Function (FName "GHCziBase.neInt") Nothing (Just 0) [rp "a", rp "b"] (AsmBlock
      [boxIntResult "x" :<=: (EvalRef (rv "a"), [])
      ,boxIntResult "y" :<=: (EvalRef (rv "b"), [])
      ,"z" :<-?: RunCmpOp (OpName "zszezh") (pv "x") (pv "y")]
      (BoolReturn "z" (ConTag (CName "GHCziBool.True")) (ConTag (CName "GHCziBool.False"))))
    )
  ,((("GHCziBase","leInt"), ([RefType, RefType], RealFun RefType)),
    Function (FName "GHCziBase.leInt") Nothing (Just 0) [rp "a", rp "b"] (AsmBlock
      [boxIntResult "x" :<=: (EvalRef (rv "a"), [])
      ,boxIntResult "y" :<=: (EvalRef (rv "b"), [])
      ,"z" :<-?: RunCmpOp (OpName "zlzezh") (pv "x") (pv "y")]
      (BoolReturn "z" (ConTag (CName "GHCziBool.True")) (ConTag (CName "GHCziBool.False"))))
    )
  ]