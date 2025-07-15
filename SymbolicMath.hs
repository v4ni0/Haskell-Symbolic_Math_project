import Data.Char(isDigit, isLetter, isUpper)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import Control.Monad.Combinators.Expr
import Control.Monad
        
data Expr = Const Double
          | Var String
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          | Pow Expr Expr
          deriving (Eq)

instance Show Expr where
    show (Const x) = show x
    show (Var x) = x
    show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
    show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
    show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
    show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
    show (Pow x y) = "(" ++ show x ++ " ^ " ++ show y ++ ")"

isVar ::Expr-> Bool
isVar (Var x) = True 
isVar _ = False

stringToDouble :: String -> Double
stringToDouble str = read str :: Double

isPartOfNumber :: Char -> Bool
isPartOfNumber x = isDigit x || x == '.'


isOperation :: Char -> Bool
isOperation x = elem x ['+','-','*','/','^']

isLeftBracket :: Char -> Bool
isLeftBracket x = x == '('

isRightBracket :: Char -> Bool
isRightBracket x = x == ')'

--прочитане на израз(приемаме че променливите започват с главна буква и продължават с малка буква или цифра)
type Parser = Parsec Void String

-- Space consumer
sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- Basic parsers
parseNumber :: Parser Expr
parseNumber = Const . read <$> lexeme (some (satisfy isPartOfNumber))

parseVariable :: Parser Expr
parseVariable = Var <$> lexeme ((:) <$> satisfy isUpper <*> many (satisfy (\c -> isDigit c || isLetter c)))

parens :: Parser a -> Parser a
parens = between (lexeme (char '(')) (lexeme (char ')'))

term :: Parser Expr
term = choice
    [ parens expr
    , parseNumber
    , parseVariable
    ]

expr :: Parser Expr
expr = makeExprParser term operatorTable

operatorTable :: [[Operator Parser Expr]]
operatorTable =
    [ [ InfixR (Pow <$ lexeme (char '^')) ]
    , [ InfixL (Mul <$ lexeme (char '*'))
      , InfixL (Div <$ lexeme (char '/')) ]
    , [ InfixL (Add <$ lexeme (char '+'))
      , InfixL (Sub <$ lexeme (char '-')) ]
    ]

-- Top level parse function

extractExpr :: String -> Expr
extractExpr str = case toParse str of
    Left err -> error (errorBundlePretty err)
    Right expr -> expr

toParse :: String -> Either (ParseErrorBundle String Void) Expr
toParse = parse (sc *> expr <* eof) ""


-- Add to main
--Опростяване
simplify :: Expr -> Expr
simplify expr = let simplified = simplifyHelper expr
                in if simplified == expr then simplified else simplify simplified
                
simplifyHelper :: Expr -> Expr
simplifyHelper (Const x) = Const x
simplifyHelper (Var x) = Var x
simplifyHelper (Add x y) = simplifyAdd (simplifyHelper x) (simplifyHelper y)
simplifyHelper (Sub x y) = simplifySub (simplifyHelper x) (simplifyHelper y)
simplifyHelper (Mul x y) = simplifyMul (simplifyHelper x) (simplifyHelper y)
simplifyHelper (Div x y) = simplifyDiv (simplifyHelper x) (simplifyHelper y)
simplifyHelper (Pow x y) = simplifyPow (simplifyHelper x) (simplifyHelper y)

--Събиране
simplifyAdd :: Expr->Expr->Expr
simplifyAdd (Const 0) x = x
simplifyAdd x (Const 0) = simplify x
simplifyAdd (Const x) (Const y) = Const (x + y)
simplifyAdd x (Const y) = Add (Const y) x
simplifyAdd (Mul (Const a) x) (Mul (Const b) y) = if x==y then Mul (Const (a+b)) x else Add (Mul (Const a) x) (Mul (Const b) y)
simplifyAdd x (Mul y z) = if x==z then Mul (Add (Const 1) y) z else Add x (Mul y z)
simplifyAdd x (Add y z) = Add (Add x y) z
simplifyAdd x y = if x==y then (Mul (Const 2) x) else Add x y

--Изваждане
simplifySub :: Expr->Expr->Expr
simplifySub x (Const 0) = x
simplifySub (Const 0) x =  (Mul (Const (-1)) x)
simplifySub  (Const x) (Const y) = Const (x - y)
--промяна--simplifyAdd (Var x) (Var y) = if x==y then Mul (Const 2) (Var x) else Add (Var x) (Var y)
simplifySub (Add (Const x) y) (Const z) = Add (Const (x-z)) y
simplifySub (Var x) (Var y) = if x==y then (Const 0) else (Sub (Var x) (Var y))
simplifySub (Mul (Const a) x) (Mul (Const b) y) = if x==y then Mul (Const (a-b)) x else Sub (Mul (Const a) x) (Mul (Const b) y)
simplifySub x y = if x==y then (Const 0) else Add x (Mul (Const (-1)) y)

--Умножение
simplifyMul :: Expr->Expr->Expr
simplifyMul (Const 0) _ = Const 0
simplifyMul _ (Const 0) = Const 0
simplifyMul (Const 1) x = x
simplifyMul  x (Const 1) = x
simplifyMul (Const x) (Const y) = Const (x * y)
simplifyMul (Pow x y) (Pow a b) = if x == a then Pow x (Add y b) else Mul (Pow x y) (Pow a b)
simplifyMul x (Const y) = Mul (Const y) x
simplifyMul (Var x) (Var y) --за по-лесна подредба на променливите
    | x > y = (Mul (Var x) (Var y)) 
    | x < y = (Mul (Var y) (Var x))
    |otherwise = (Pow (Var x) (Const 2))
simplifyMul x (Div (Const y) z) = Div (Mul x (Const y)) z
simplifyMul (Const x) (Div y (Const z)) = Mul (Const (x/z)) y
simplifyMul (Const x) (Mul (Const y) z) =  Mul (Const (x*y)) z
simplifyMul (Mul (Const x) y) z = Mul (Const x) (Mul y z)
simplifyMul (Var x) (Mul (Var y) z)
    | x < y = Mul (Var y) (Mul (Var x) z)
    | otherwise  = Mul (Var x) (Mul (Var y) z)
simplifyMul (Mul x y) z =  Mul x (Mul y z) 
simplifyMul (Pow x y) z =Mul z (Pow x y)
simplifyMul x y = Mul x y

--Деление
findCommonFactors :: Expr -> Expr -> Maybe Expr
findCommonFactors (Mul x y) (Mul a b)
    |x==a = Just x
    |x==b = Just x
    |y==a = Just y
    |y==b = Just y
    |otherwise = findCommonFactors x a `mplus` findCommonFactors x b `mplus` findCommonFactors y a `mplus` findCommonFactors y b
findCommonFactors x (Mul y z) = if x == y || x == z  then Just x else findCommonFactors x z `mplus` findCommonFactors x y
findCommonFactors (Mul x y) z = if x == z || y == z then Just z else findCommonFactors x z `mplus` findCommonFactors y z
findCommonFactors x y = if x == y then Just x else Nothing

isDivisibleByX :: Expr -> Expr -> Bool
isDivisibleByX (Mul x y) z = x == z || y == z ||(Mul x y) == z ||(Mul y x) ==z ||isDivisibleByX x z || isDivisibleByX y z
isDivisibleByX x y = x == y

simplifyDiv :: Expr->Expr->Expr
simplifyDiv _ (Const 0) = error "Division by zero"
simplifyDiv (Const 0) _ = Const 0
simplifyDiv x (Const 1) = x
simplifyDiv (Const x) (Const y) = Const (x/y)
simplifyDiv (Var x) (Var y) = if x == y then Const 1 else Div (Var x) (Var y)
simplifyDiv (Div x y) z = Div x (Mul y z)
simplifyDiv (Mul (Const x) y) (Const a) = Mul (Const (x/a)) y
simplifyDiv (Mul (Const x) y) (Mul (Const a) b) = Mul (Const (x/a)) (Div y b)
simplifyDiv (Mul x y) (Mul a b)
    |(Mul x y) == (Mul a b) = Const 1
    |x == a = Div y b
    |x == b = Div y a
    |y == a = Div x b
    |y == b = Div x a
    |otherwise = case findCommonFactors (Mul x y) (Mul a b) of
        Just factor -> if isDivisibleByX x factor && isDivisibleByX a factor
            then Div (Mul (Div x factor) y) (Mul (Div a factor) b)
            else if isDivisibleByX x factor && isDivisibleByX b factor
            then Div (Mul (Div x factor) y) (Mul a (Div b factor))
            else if isDivisibleByX y factor && isDivisibleByX a factor
            then Div (Mul x (Div y factor)) (Mul (Div a factor) b)
            else Div (Mul x (Div y factor)) (Mul a (Div b factor))
        Nothing -> Div (Mul x y) (Mul a b)
simplifyDiv (Mul x y) z
    |(Mul x y) == z = Const 1
    |x == z = y
    |y == z = x
    |otherwise = case findCommonFactors (Mul x y) z of
        Just factor -> if isDivisibleByX x factor
            then Div (Mul (Div x factor) y) (Div z factor)
            else Div (Mul x (Div y factor)) (Div z factor)
        Nothing -> Div (Mul x y) z
simplifyDiv x (Mul y z) 
    |(Mul y z) == x = Const 1
    |y == x = Div (Const 1) z
    |z == x = Div (Const 1) y
    |otherwise = case findCommonFactors x (Mul y z) of
        Just factor -> if isDivisibleByX y factor
            then Div (Div x factor) (Mul y (Div z factor))
            else Div (Div x factor) (Mul z (Div y factor))
        Nothing -> Div x (Mul y z)

simplifyDiv x y = if x==y then Const 1 else Div x y

--Степенуване
simplifyPow :: Expr->Expr->Expr
simplifyPow _ (Const 0) = Const 1
simplifyPow (Const 1) _ = Const 1
simplifyPow x (Const 1) =  x
simplifyPow (Const 0) _ = Const 0
simplifyPow (Const x) (Const y) = Const (x ** y)
simplifyPow (Pow x y) z = Pow x (Mul y z)
simplifyPow x y = Pow x y

--Разкриване на скоби
expandBrackets :: Expr -> Expr
expandBrackets expr = if new == expr then expr else expandBracketsHelper new
        where new = expandBracketsHelper expr

expandBracketsHelper :: Expr -> Expr
expandBracketsHelper (Add x y) = Add (expandBracketsHelper x) (expandBracketsHelper y)
expandBracketsHelper (Sub x y) = Sub (expandBracketsHelper x) (expandBracketsHelper y)
expandBracketsHelper (Mul x y) = distributeMul (expandBracketsHelper x) (expandBracketsHelper y)
expandBracketsHelper (Div x y) = distributeDiv (expandBracketsHelper x) (expandBracketsHelper y)
expandBracketsHelper (Pow x y) = Pow (expandBracketsHelper x) (expandBracketsHelper y)
expandBracketsHelper x = x

distributeMul :: Expr -> Expr -> Expr
distributeMul (Add x y) z = Add (distributeMul x z) (distributeMul y z)
distributeMul (Sub x y) z = Sub (distributeMul x z) (distributeMul y z)
distributeMul z (Add x y) = Add (distributeMul z x) (distributeMul z y)
distributeMul z (Sub x y) = Sub (distributeMul z x) (distributeMul z y)
distributeMul x y = Mul x y

distributeDiv :: Expr -> Expr -> Expr
distributeDiv (Add x y) z = Add (distributeDiv x z) (distributeDiv y z)
distributeDiv (Sub x y) z = Sub (distributeDiv x z) (distributeDiv y z)
distributeDiv z (Add x y) = Add (distributeDiv z x) (distributeDiv z y)
distributeDiv z (Sub x y) = Sub (distributeDiv z x) (distributeDiv z y)
distributeDiv x y = Div x y


--привеждане под общ знаменател
findCommonDenominator :: Expr -> Expr
findCommonDenominator expr =  if new == expr then expr else findCommonDenominatorHelper new
            where new = simplify (findCommonDenominatorHelper expr)

findCommonDenominatorHelper :: Expr -> Expr
findCommonDenominatorHelper (Add x y) = findCommonDenominatorAdd (findCommonDenominatorHelper x) (findCommonDenominator y)
findCommonDenominatorHelper (Sub x y) = findCommonDenominatorSub (findCommonDenominatorHelper x) (findCommonDenominator y)
findCommonDenominatorHelper (Mul x y) = Mul (findCommonDenominatorHelper x) (findCommonDenominatorHelper y)
findCommonDenominatorHelper (Div x y) = Div (findCommonDenominatorHelper x) (findCommonDenominatorHelper y)
findCommonDenominatorHelper x = x

findCommonDenominatorAdd :: Expr ->Expr->Expr 
findCommonDenominatorAdd (Div x y ) (Div a b) = (Div (Add (Mul x b) (Mul a y)) (Mul y b))
findCommonDenominatorAdd (Div x y) z = (Div (Add x (Mul y z)) y)
findCommonDenominatorAdd x (Div y z) = (Div (Add (Mul x z) y) z)
findCommonDenominatorAdd x y = Add x y

findCommonDenominatorSub :: Expr ->Expr->Expr
findCommonDenominatorSub (Div x y ) (Div a b) = (Div (Sub (Mul x b) (Mul a y)) (Mul y b))
findCommonDenominatorSub (Div x y) z = (Div (Sub x (Mul y z)) y)
findCommonDenominatorSub x (Div y z) = (Div (Sub (Mul x z) y) z)
findCommonDenominatorSub x y = Sub x y


-- Диференциране
differentiate :: Expr -> String -> Expr
differentiate (Const _) _ = Const 0
differentiate (Var x) var = if x == var then Const 1 else Const 0
differentiate (Add x y) var = simplify (Add (differentiate x var) (differentiate y var))
differentiate (Sub x y) var = simplify (Sub (differentiate x var) (differentiate y var))
differentiate (Mul x y) var = simplify (Add (Mul x (differentiate y var)) (Mul (differentiate x var) y))
differentiate (Div x y) var = simplify (Div (Sub (Mul (differentiate x var) y) (Mul x (differentiate y var))) (Pow y (Const 2)))
differentiate (Pow x y) var = simplify (Mul (Mul y (Pow x (Sub y (Const 1)))) (differentiate x var))

--Интегриране
integrate :: Expr -> String -> Expr
integrate (Const c) var = Mul (Const c) (Var var)
integrate (Var x) var
    | x == var = Div (Pow (Var x) (Const 2)) (Const 2)
    | otherwise = Mul (Var x) (Var var)
integrate (Pow (Var x) (Const n)) var
    | x == var = simplify (Div (Pow (Var x) (Const (n+1))) (Const (n+1)))
    | otherwise = simplify (Mul (Pow (Var x) (Const n)) (Var var))
integrate (Add x y) var = simplify (Add (integrate x var) (integrate y var))
integrate (Sub x y) var = simplify (Sub (integrate x var) (integrate y var))
integrate (Mul (Const c) x) var = simplify (Mul (Const c) (integrate x var))
integrate x _ = error $ "Cannot integrate expression: " ++ show x

--Извеждане на общ множител пред скоби
findCommonTerm :: Expr ->  Maybe Expr
findCommonTerm (Add x y) = findCommonFactors x y
findCommonTerm (Sub x y) = findCommonFactors x y
findCommonTerm _ = Nothing

divideByTerm :: Expr -> Expr -> Expr
divideByTerm (Mul x y) term
    | x == term = y
    | y == term = x
    | otherwise = if isDivisibleByX x term
        then Mul (divideByTerm x term) y
        else Mul x (divideByTerm y term)
divideByTerm expr term = if expr == term then (Const 1) else expr

factorOut :: Expr -> Expr
factorOut expr  = if new == expr then expr else factorOutHelper new
        where new = factorOutHelper expr

factorOutHelper :: Expr -> Expr
factorOutHelper (Add x y) = case findCommonTerm (Add x y) of
    Just term -> Mul term (Add (divideByTerm x term) (divideByTerm y term))
    Nothing -> Add (factorOutHelper x) (factorOutHelper y)
factorOutHelper (Sub x y) = case findCommonTerm (Sub x y) of
    Just term -> Mul term (Sub (divideByTerm x term) (divideByTerm y term))
    Nothing -> Sub (factorOutHelper x) (factorOutHelper y)
factorOutHelper (Mul x y) = Mul (factorOutHelper x) (factorOutHelper y)
factorOutHelper (Div x y) = Div (factorOutHelper x) (factorOutHelper y)
factorOutHelper (Pow x y) = Pow (factorOutHelper x) y
factorOutHelper x = x

--Изчисляване на израз
evaluate :: Expr ->[(String, Double)]-> Expr
evaluate expr [] = expr
evaluate expr (x:xs) = simplify (evaluate (evaluateVar expr x) xs)

evaluateVar ::Expr->(String,Double)->Expr
evaluateVar (Var x) (var, val) = if x == var then (Const val) else (Var x)
evaluateVar (Const x) _ = (Const x)
evaluateVar (Add x y) (var, val) = (Add (evaluateVar x (var, val)) (evaluateVar y (var, val)))
evaluateVar (Sub x y) (var, val) = (Sub (evaluateVar x (var, val)) (evaluateVar y (var, val)))
evaluateVar (Mul x y) (var, val) = (Mul (evaluateVar x (var, val)) (evaluateVar y (var, val)))
evaluateVar (Div x y) (var, val) = (Div (evaluateVar x (var, val)) (evaluateVar y (var, val)))
evaluateVar (Pow x y) (var, val) = (Pow (evaluateVar x (var, val)) (evaluateVar y (var, val)))


testFactorOut :: IO ()
testFactorOut = do
    let example1 = extractExpr "2*X + 2*Y" 
    print $ "Initial expression: " ++ show example1 ++ " After factoring out: " ++ show (factorOut example1)
    let example2 = extractExpr "X*Y + X*Z" 
    print $ "Initial expression: " ++ show example2 ++ " After factoring out: " ++ show (factorOut example2)
    let example3 = extractExpr "Y*X*3 + 3*X*Z"  
    print $ "Initial expression: " ++ show example3 ++ " After factoring out: " ++ show (factorOut example3)
    let example4 = extractExpr "2*X*Y + 2*X*Z + 2*X*W"  
    print $ "Initial expression: " ++ show example4 ++ " After factoring out: " ++ show (factorOut example4)
    let example5 = extractExpr "X*Y - X*Z"  
    print $ "Initial expression: " ++ show example5 ++ " After factoring out: " ++ show (factorOut example5)


testCommonDenominator :: IO ()
testCommonDenominator = do
    let example1 = extractExpr "X/2 + Y/3"
    print $ "Initial expression: " ++ show example1 ++ " After finding common denominator: " ++ show (findCommonDenominator example1)
    let example2 = extractExpr "1/X + 1/Y"
    print $ "Initial expression: " ++ show example2 ++ " After finding common denominator: " ++ show (findCommonDenominator example2)
    let example3 = extractExpr "(A/B) + (C/D)"
    print $ "Initial expression: " ++ show example3 ++ " After finding common denominator: " ++ show (findCommonDenominator example3)
    let example4 = extractExpr "X/2 - Y/4"
    print $ "Initial expression: " ++ show example4 ++ " After finding common denominator: " ++ show (findCommonDenominator example4)
    let example5 = extractExpr "(A/B) + (C/D) + (E/F)"
    print $ "Initial expression: " ++ show example5 ++ " After finding common denominator: " ++ show (findCommonDenominator example5)
    let example6 = extractExpr "(X/Y) + (Y/Z) + (Z/X)"
    print $ "Initial expression: " ++ show example6 ++ " After finding common denominator: " ++ show (findCommonDenominator example6)

testEvaluate :: IO ()
testEvaluate = do
    let example1 = extractExpr "2 + 3 * X"
    print $ "Initial expression: " ++ show example1 ++ " After evaluation with X=4: " ++ show (evaluate example1 [("X", 4)])
    let example2 = extractExpr "X^2 + 3*X + 4"
    print $ "Initial expression: " ++ show example2 ++ " After evaluation with X=2: " ++ show (evaluate example2 [("X", 2)])
    let example3 = extractExpr "2*X + 3*Y"
    print $ "Initial expression: " ++ show example3 ++ " After evaluation with X=1, Y=2: " ++ show (evaluate example3 [("X", 1), ("Y", 2)])
    let example4 = extractExpr "X*Y + Y^2"
    print $ "Initial expression: " ++ show example4 ++ " After evaluation with X=3, Y=4: " ++ show (evaluate example4 [("X", 3), ("Y", 4)])
    let example5 = extractExpr "X + Y + Z"
    print $ "Initial expression: " ++ show example5 ++ " After evaluation with X=1, Y=2, Z=3: " ++ show (evaluate example5 [("X", 1), ("Y", 2), ("Z", 3)])

testExpand :: IO ()
testExpand = do
    let example1 = extractExpr "(2 + 3) / 4"
    print $ "Initial expression: " ++ show example1 ++ " After expanding: " ++ show (expandBrackets example1)
    let example2 = extractExpr "(5 - 2) * 3"
    print $ "Initial expression: " ++ show example2 ++ " After expanding: " ++ show (expandBrackets example2)
    let example3 = extractExpr "(X + 3) * (Y + 2)"
    print $ "Initial expression: " ++ show example3 ++ " After expanding: " ++ show (expandBrackets example3)
    let example4 = extractExpr "((X * Y) + 3) * (Z - 2)"
    print $ "Initial expression: " ++ show example4 ++ " After expanding: " ++ show (expandBrackets example4)
    let example5 = extractExpr "(((((D * A) + (C * B)) * F) + (E * (D * B))) / (F * (D * B)))"
    print $ "Initial expression: " ++ show example5 ++ " After expanding: " ++ show (expandBrackets example5)

testIntegrate :: IO ()
testIntegrate = do
    let example1 = extractExpr "2"
    print $ "Initial expression: " ++ show example1 ++ " After integration wrt X: " ++ show (integrate example1 "X")
    let example2 = extractExpr "X"
    print $ "Initial expression: " ++ show example2 ++ " After integration wrt X: " ++ show (integrate example2 "X")
    let example3 = extractExpr "X^2"
    print $ "Initial expression: " ++ show example3 ++ " After integration wrt X: " ++ show (integrate example3 "X")
    let example4 = extractExpr "2*X"
    print $ "Initial expression: " ++ show example4 ++ " After integration wrt X: " ++ show (integrate example4 "X")
    let example5 = extractExpr "X + 1"
    print $ "Initial expression: " ++ show example5 ++ " After integration wrt X: " ++ show (integrate example5 "X")

testDifferentiate :: IO ()
testDifferentiate = do
    let example1 = extractExpr "2 + 3 * X"
    print $ "Initial expression: " ++ show example1 ++ " After differentiation wrt X: " ++ show (differentiate example1 "X")
    let example2 = extractExpr "X^2 + 3*X + 4"
    print $ "Initial expression: " ++ show example2 ++ " After differentiation wrt X: " ++ show (differentiate example2 "X")
    let example3 = extractExpr "2*X + 3*X^2 + 4*X^3"
    print $ "Initial expression: " ++ show example3 ++ " After differentiation wrt X: " ++ show (differentiate example3 "X")
    let example4 = extractExpr "X*Y + Y^2"
    print $ "Initial expression: " ++ show example4 ++ " After differentiation wrt X: " ++ show (differentiate example4 "X")
    print $ "Initial expression: " ++ show example4 ++ " After differentiation wrt Y: " ++ show (differentiate example4 "Y")
    let example5 = extractExpr "(2*X+Y)^3"
    print $ "Initial expression: " ++ show example5 ++ " After differentiation wrt X: " ++ show (differentiate example5 "X")

testToParse :: IO ()
testToParse = do
    print $ toParse "2+(X*8^389*(Yjni8y+Z))"
    print $ toParse "2 + 3 * 4"

testSimplify :: IO ()
testSimplify = do
    let example1 = extractExpr "2 + 3 * 4"
    print $ "Initial expression: " ++ show example1 ++ " After simplifying: " ++ show (simplify example1)
    let example2= extractExpr "2*X + 3*X + 4*X" 
    print $ "Initial expression: " ++ show example2 ++ " After simplifying: " ++ show (simplify example2)
    let example3 =extractExpr "2*X + 3*X + 4*X"
    print $ "Initial expression: " ++ show example3 ++ " After simplifying: " ++ show (simplify example3)
    let example4  = extractExpr "2*(3*X) + 5-5 + X*(4^2^1)"
    print $ "Initial expression: " ++ show example4 ++ " After simplifying: " ++ show (simplify example4)
    let example5 = extractExpr "2*(3*X) -2*(3*X)"
    print $ "Initial expression: " ++ show example5 ++ " After simplifying: " ++ show (simplify example5)
    let example6 = extractExpr "X*Y*A*2*H*R + 3*A*H*Y*R*X"
    print $ "Initial expression: " ++ show example6 ++ " After simplifying: " ++ show (simplify example6)
    let example7 = extractExpr "(10*X*Y+5*Y*X)/(5*X*Y*Z)"
    print $ "Initial expression: " ++ show example7 ++ " After simplifying: " ++ show (simplify example7)
    let example9 = extractExpr "2*(3*X + 4*Y) - 2*(3*X + 4*Y)"
    print $ "Initial expression: " ++ show example9 ++ " After simplifying: " ++ show (simplify example9)
    let example10 = extractExpr "X*Y*A*2*H*R + 3*A*H*Y*R*X - X*Y*A*2*H*R"
    print $ "Initial expression: " ++ show example10 ++ " After simplifying: " ++ show (simplify example10)
    let example11 = extractExpr "(10*X*Y+5*Y*X)/(5*X*Y*Z)+ 10+(10*X*Y+5*Y*X)/(5*X*Y*Z) -10"
    print $ "Initial expression: " ++ show example11 ++ " After simplifying: " ++ show (simplify example11)
    let example12 = extractExpr "X^6*Y*X^2 - Y*X^8"
    print $ "Initial expression: " ++ show example12 ++ " After simplifying: " ++ show (simplify example12)

main :: IO() 
main  = do 
    testSimplify
    putStrLn "Enter an expression:"
    str <- getLine
    let expr = extractExpr str
    putStrLn "\nChoose operation:"
    putStrLn "1. Simplify"
    putStrLn "2. Expand brackets"
    putStrLn "3. Factor out common terms"
    putStrLn "4. Find common denominator"
    putStrLn "5. Differentiate"
    putStrLn "6. Integrate"
    putStrLn "7. Exit"
    putStrLn "Enter operation number (1-7): "
    
    number <- getLine
    case number of
        "1" -> putStrLn $ "Result: " ++ show (simplify expr)
        "2" -> putStrLn $ "Result: " ++ show (expandBrackets expr)
        "3" -> putStrLn $ "Result: " ++ show (factorOut expr)
        "4" -> putStrLn $ "Result: " ++ show (findCommonDenominator expr)
        "5" -> do
            putStrLn "Enter variable to differentiate: "
            var <- getLine
            putStrLn $ "Result: " ++ show (differentiate expr var)
        "6" -> do
            putStrLn "Enter variable to integrate: "
            var <- getLine
            putStrLn $ "Result: " ++ show (integrate expr var)
        "7" -> return ()
        
    
    
   
    
