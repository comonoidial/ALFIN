module Alfin.Builtins where

import Alfin.Syntax
import Alfin.LowCore

data FunKind
  = RealFun ShapeType
  | FixFun ShapeType
  | UnboxFun String   -- real function with unboxed type as result
  | SelFun QName Int  -- ConName, index
  | IdFun
  | PrimFun ShapeType
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

defaultPrimBox :: String -> ConName
defaultPrimBox "Int" = ConName "GHCziTypes.Izh"

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
  ,(("GHCziPrim","zmzh"), ([PType "Int", PType "Int"], PrimFun (PType "Int")))
  ,(("GHCziPrim","zpzh"), ([PType "Int", PType "Int"], PrimFun (PType "Int")))
  ,(("GHCziPrim","ztzh"), ([PType "Int", PType "Int"], PrimFun (PType "Int")))
  ,(("GHCziPrim","negateIntzh"), ([PType "Int"], PrimFun (PType "Int")))
  ,(("GHCziBase","modIntzh"), ([PType "Int", PType "Int"], PrimFun (PType "Int")))
-- workaround to support some error throwing functions
  ,(("GHCziErr","overflowError"), ([], ErrFun 1))
  ,(("GHCziErr","divZZeroError"), ([], ErrFun 2))
  ,(("ControlziExceptionziBase","patError"), ([RefType], ErrFun 3))
  ,(("GHCziList","badHead"), ([], ErrFun 4))
  ]

compareFuns :: [QName]
compareFuns = map fst $ filter ((==CmpFun) . snd . snd) baseFuns

boxIntTag :: NodeTag
boxIntTag = Box (ConName "GHCziTypes.Izh")

--boxIntResult :: String -> (CallResultRef, Maybe (NodeTag, [Parameter], FetchHint))
--boxIntResult x = (dummyResultRef, Just (boxIntTag, [pp x], Nothing))

builtinPrimOps :: [((QName, ([ShapeType], FunKind)), Definition)]
builtinPrimOps =
  [((("GHCziBase","unpackCStringzh"), ([RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.unpackCStringzh") Nothing [rv "x"] (Block [] (Jump (Eval "x") [])))
 {-
  ,((("Flite","str"), ([RefType], RealFun RefType)),
    Definition (FunName "Flite.str") Nothing [rv "ys"] (Block [] (Case (Eval (rv "ys")) [] (dummyResultRef) Nothing
    [((ConName "GHCziTypes.ZMZN"), [], Nothing, Block [] (Return (Con (ConName "Flite.Nil")) []))
    ,((ConName "GHCziTypes.ZC"), [rv "x", rv "xs"], Nothing, Block 
      [(dummyResultRef, Just (Box (ConName "GHCziTypes.Czh"), [pv "c"], Nothing)) :<=: (Eval (rv "x"), [])
      ,"z" :<-: Store (boxIntTag) [pv "c"]
      ,"zs" :<-: Store (Fun $ FunName "Flite.str") [rv "xs"]
      ] (Return (Con (ConName "Flite.Cons")) [rv "z", rv "zs"]))
    ])))
  ,((("Flite","emit"), ([RefType, RefType], RealFun RefType)),
   Definition (FName "Flite.emit") Nothing [rv "i", rv "k"] (Block
     [boxIntResult "x" :<=: (Eval (rv "i"), [])
     ,Send (Con (ConName "GHCziTypes.Czh")) [pv "x"]]
     (Jump (Eval (rv "k")) [])
    ))
  ,((("GHCziBase","plusInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.plusInt") Nothing [rv "a", rv "b"] (Block
      [boxIntResult "x" :<=: (Eval (rv "a"), [])
      ,boxIntResult "y" :<=: (Eval (rv "b"), [])
      ,"z" :<~: RunPrimOp (Operator "zpzh") (pv "x") (Just $ pv "y")]
      (Return boxIntTag [pv "z"]))
    )
  ,((("GHCziBase","minusInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.minusInt") Nothing [rv "a", rv "b"] (Block
      [boxIntResult "x" :<=: (Eval (rv "a"), [])
      ,boxIntResult "y" :<=: (Eval (rv "b"), [])
      ,"z" :<~: RunPrimOp (Operator "zmzh") (pv "x") (Just $ pv "y")]
      (Return boxIntTag [pv "z"]))
    )
  ,((("GHCziBase","timesInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.timesInt") Nothing [rv "a", rv "b"] (Block
      [boxIntResult "x" :<=: (Eval (rv "a"), [])
      ,boxIntResult "y" :<=: (Eval (rv "b"), [])
      ,"z" :<~: RunPrimOp (Operator "ztzh") (pv "x") (Just $ pv "y")]
      (Return boxIntTag [pv "z"]))
    )
  ,((("GHCziBase","eqInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.eqInt") Nothing [rv "a", rv "b"] (Block
      [boxIntResult "x" :<=: (Eval (rv "a"), [])
      ,boxIntResult "y" :<=: (Eval (rv "b"), [])
      ,"z" :<-?: RunCmpOp (Operator "zezezh") (pv "x") (pv "y")]
      (BoolReturn "z" (Con (ConName "GHCziBool.True")) (Con (ConName "GHCziBool.False"))))
    )
  ,((("GHCziBase","neInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.neInt") Nothing [rv "a", rv "b"] (Block
      [boxIntResult "x" :<=: (Eval (rv "a"), [])
      ,boxIntResult "y" :<=: (Eval (rv "b"), [])
      ,"z" :<-?: RunCmpOp (Operator "zszezh") (pv "x") (pv "y")]
      (BoolReturn "z" (Con (ConName "GHCziBool.True")) (Con (ConName "GHCziBool.False"))))
    )
  ,((("GHCziBase","leInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.leInt") Nothing [rv "a", rv "b"] (Block
      [boxIntResult "x" :<=: (Eval (rv "a"), [])
      ,boxIntResult "y" :<=: (Eval (rv "b"), [])
      ,"z" :<-?: RunCmpOp (Operator "zlzezh") (pv "x") (pv "y")]
      (BoolReturn "z" (Con (ConName "GHCziBool.True")) (Con (ConName "GHCziBool.False"))))
    )
  -}
  ]