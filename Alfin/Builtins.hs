module Alfin.Builtins where

import Alfin.Syntax
import Alfin.LowCore

data FunKind
  = RealFun ShapeType
  | FixFun ShapeType
  | UnboxFun String   -- real function with unboxed primitive as result
  | SelFun QName Int  -- ConName, index
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

defaultPrimBox :: String -> NodeTag
defaultPrimBox "Int" = Con (ConName "GHCziTypes.Izh")

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
boxIntTag = Con (ConName "GHCziTypes.Izh")

unBoxIntCase :: String -> CallExpr -> Block -> Block
unBoxIntCase n cx b = Block [] (Case cx [] [(ConPat (ConName "GHCziTypes.Izh") [pv n] , b)])

builtinPrimOps :: [((QName, ([ShapeType], FunKind)), Definition)]
builtinPrimOps =
  [((("GHCziBase","unpackCStringzh"), ([RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.unpackCStringzh") Nothing [rv "x"] (Block [] (Jump (Eval "x") [])))
  ,((("Flite","str"), ([RefType], RealFun RefType)),
    Definition (FunName "Flite.str") Nothing [rv "ys"] (Block [] (Case (Eval "ys") [] 
    [(ConPat (ConName "GHCziTypes.ZMZN") [], Block [] (Return (Con (ConName "Flite.Nil")) []))
    ,(ConPat (ConName "GHCziTypes.ZC") [rv "x", rv "xs"], Block []
      (Case (Eval "x") [] [(ConPat (ConName "GHCziTypes.Izh") [pv "c"], Block
        [rv "z" := Store (boxIntTag) [pv "c"]
        ,rv "zs" := Store (Fun (FunName "Flite.str") Upd) [rv "xs"]
        ] (Return (Con (ConName "Flite.Cons")) [rv "z", rv "zs"]))
      ]))])))
  ,((("Flite","emit"), ([RefType, RefType], RealFun RefType)),
   Definition (FunName "Flite.emit") Nothing [rv "i", rv "k"] $
     unBoxIntCase "x" (Eval "i") $ Block 
       [Send (Con (ConName "GHCziTypes.Czh")) [pv "x"]]
       (Jump (Eval "k") [])
    )
  ,((("GHCziBase","plusInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.plusInt") Nothing [rv "a", rv "b"] $
      unBoxIntCase "x" (Eval "a") $
      unBoxIntCase "y" (Eval "b") $ Block
      [pv "z" := PrimOp (Operator "zpzh") [pv "x", pv "y"]]
      (Return boxIntTag [pv "z"])
    )
  ,((("GHCziBase","minusInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.minusInt") Nothing [rv "a", rv "b"] $
      unBoxIntCase "x" (Eval "a") $
      unBoxIntCase "y" (Eval "b") $ Block
      [pv "z" := PrimOp (Operator "zmzh") [pv "x", pv "y"]]
      (Return boxIntTag [pv "z"])
    )
  ,((("GHCziBase","timesInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.timesInt") Nothing [rv "a", rv "b"] $
      unBoxIntCase "x" (Eval "a") $
      unBoxIntCase "y" (Eval "b") $ Block
      [pv "z" := PrimOp (Operator "ztzh") [pv "x", pv "y"]]
      (Return boxIntTag [pv "z"])
    )
  ,((("GHCziBase","eqInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.eqInt") Nothing [rv "a", rv "b"] $
      unBoxIntCase "x" (Eval "a") $
      unBoxIntCase "y" (Eval "b") $ Block
      [bv "z" := PrimOp (Operator "zezezh") [pv "x", pv "y"]]
      (Cond "z" 
        (Block [] (Return (Con (ConName "GHCziBool.True" )) []))
        (Block [] (Return (Con (ConName "GHCziBool.False")) [])))
    )
  ,((("GHCziBase","neInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.neInt") Nothing [rv "a", rv "b"] $
      unBoxIntCase "x" (Eval "a") $
      unBoxIntCase "y" (Eval "b") $ Block
      [bv "z" := PrimOp (Operator "zszezh") [pv "x", pv "y"]]
      (Cond "z" 
        (Block [] (Return (Con (ConName "GHCziBool.True" )) []))
        (Block [] (Return (Con (ConName "GHCziBool.False")) [])))
    )
  ,((("GHCziBase","leInt"), ([RefType, RefType], RealFun RefType)),
    Definition (FunName "GHCziBase.leInt") Nothing [rv "a", rv "b"] $
      unBoxIntCase "x" (Eval "a") $
      unBoxIntCase "y" (Eval "b") $ Block
      [bv "z" := PrimOp (Operator "zlzezh") [pv "x", pv "y"]]
      (Cond "z" 
        (Block [] (Return (Con (ConName "GHCziBool.True" )) []))
        (Block [] (Return (Con (ConName "GHCziBool.False")) [])))
    )
  ]