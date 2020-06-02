module Rule
where

import Data.List

infix 6 :->
data Rule = Char :-> [Char]
    deriving (Eq)

instance Show Rule where
    show (v :-> s) = [v] ++ " -> " ++ (if s == lambda then "λ" else s)

getLhs :: Rule -> Char
getLhs (v :-> _) = v

getRhs :: Rule -> [Char]
getRhs (_ :-> s) = s

printRules :: [Rule] -> IO ()
printRules rs = do
    let lhs = nub $ [getLhs rule | rule <- rs]
    let formatRhs (_ :-> s) = if s == lambda then "λ" else s
    let rs' = [ (v, map (formatRhs) $ getRulesFor rs v) | v <- lhs ]
    mapM_ putStrLn $ map (\(v, s) -> [v] ++ " -> " ++ (intercalate "|" s)) rs'

isVariable :: Char -> Bool
isVariable c = elem c ['A'..'Z']

isTerminal :: Char -> Bool
isTerminal c = elem c ['a'..'z']

lambda :: [Char]
lambda = []

-- >>> getRulesFor rules 'A'
-- [A -> C,A -> a]
--
getRulesFor :: [Rule] -- ^ Production rules
            -> Char   -- ^ Variable
            -> [Rule] -- ^ Rules for the given variable
getRulesFor (rule@(v' :-> _):rs) v
    | v == v'   = rule:getRulesFor rs v
    | otherwise = getRulesFor rs v
getRulesFor _ _ = []