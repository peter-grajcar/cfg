module GrammarReduction
where

import Data.List
import Control.Monad
import Rule

-- >>> printRules rules
-- S -> SS|aAa|bBb|λ
-- A -> C|a
-- B -> C|b
-- C -> CDE|λ
-- D -> A|B|ab
-- F -> FA|E|λ
--
rules :: [Rule]
rules = [
        'S' :-> "SS",
        'S' :-> "aAa", 
        'S' :-> "bBb", 
        'S' :-> lambda,
        'A' :-> "C", 
        'A' :-> "a",
        'B' :-> "C", 
        'B' :-> "b",
        'C' :-> "CDE",
        'C' :-> lambda,
        'D' :-> "A", 
        'D' :-> "B", 
        'D' :-> "ab",
        'F' :-> "FA", 
        'F' :-> "E", 
        'F' :-> lambda
    ]


-- >>> any (isLambdaRule) $ getRulesFor rules 'S'
-- True
--
-- >>> any (isLambdaRule) $ getRulesFor rules 'A'
-- False
--
-- >>> map (getRulesFor rules) "CD"
-- [[C -> CDE,C -> λ],[D -> A,D -> B,D -> ab]]
--
isLambdaRule :: Rule -> Bool
isLambdaRule (_ :-> s) = s == lambda


-- >>> lambdaRules rules
-- [S -> λ,C -> λ,F -> λ]
--
lambdaRules :: [Rule] -- ^ Production rules
            -> [Rule] -- ^ Lambda rules from the production rule set
lambdaRules = filter (isLambdaRule)


genericInduction :: (Eq a) 
                 => ([a] -> a -> Bool)  -- ^ Condition used in induction step
                 -> [a]                 -- ^ Base of induction
                 -> [a]                 -- ^ Domain
                 -> [a]                 -- ^ A subset of domain satisfiing the condition
genericInduction (cond) base domain = genericClosure base
    where 
        genericClosure closure
            | closure == step   = closure
            | otherwise         = genericClosure step
            where
                step = nub $ closure ++ [x | x <- domain, cond closure x]


-- >>> nullableRules rules
-- [S -> λ,C -> λ,F -> λ,S -> SS,A -> C,B -> C,D -> A,D -> B,F -> FA]
--
nullableRules :: [Rule] -- ^ Production rules
              -> [Rule] -- ^ Nullable rules from the production rule set
nullableRules rs = genericInduction cond base rs
    where
        base = lambdaRules rs
        cond closure (_ :-> s) = all (hasNullableRule closure) s
        hasNullableRule closure var  = any (\(v :-> _) -> var == v) closure
               


-- >>> filter (not . isUnitRule) rules
-- [S -> SS,S -> aAa,S -> bBb,S -> λ,A -> a,B -> b,C -> CDE,C -> λ,D -> ab,F -> FA,F -> λ]
--
isUnitRule :: Rule -> Bool
isUnitRule (_ :-> s) = (length s == 1) && (isVariable $ head s)

-- >>> unitRules rules
-- [('S','S'),('A','A'),('B','B'),('C','C'),('D','D'),('F','F'),('A','C'),('B','C'),('D','A'),('D','B'),('F','E')]
--
unitRules :: [Rule]         -- ^ Production rules
          -> [(Char, Char)] -- ^ List of unit pairs
unitRules [] = []
unitRules rs = trivial ++ nonTrivial rs
    where 
        trivial = nub $ [(v, v) | (v :-> _) <- rs]
        nonTrivial [] = []
        nonTrivial (rule@(v :-> s):rs') =   if isUnitRule rule then
                                                (v, head s):nonTrivial rs'
                                            else
                                                nonTrivial rs'




-- >>> transitiveClosure [(1, 2), (2, 3), (3, 4)]
-- [(1,2),(2,3),(3,4),(1,3),(2,4),(1,4)]
--
-- >>> transitiveClosure $ unitRules rules
-- [('S','S'),('A','A'),('B','B'),('C','C'),('D','D'),('F','F'),('A','C'),('B','C'),('D','A'),('D','B'),('F','E'),('D','C')]
--
transitiveClosure :: (Eq a) => [(a, a)] -> [(a, a)]
transitiveClosure closure
    | closure == step   = closure
    | otherwise         = transitiveClosure step
    where
        step = nub $ closure ++ [(a, c) | (a, b) <- closure, (b', c) <- closure, b == b']



-- >>> tail $ pset [1, 2, 3]
-- [[3],[2],[2,3],[1],[1,3],[1,2],[1,2,3]]
--
pset :: [a] -> [[a]]
pset = filterM (\_ -> [False, True])

-- >>> nullableRules rules
-- >>> filter (\(_ :-> s) -> s /= lambda) $ nullableRules rules
-- >>> nub $ concat [ [ v :-> s' | s' <- tail $ pset s ] | (v :-> s) <- filter (\(_ :-> s) -> s /= lambda) $ nullableRules rules ]
-- [S -> λ,C -> λ,F -> λ,S -> SS,A -> C,B -> C,D -> A,D -> B,F -> FA]
-- [S -> SS,A -> C,B -> C,D -> A,D -> B,F -> FA]
-- [S -> S,S -> SS,A -> C,B -> C,D -> A,D -> B,F -> A,F -> F,F -> FA]
--
-- >>> printRules $ eliminateLambdaRules rules
-- S -> aAa|bBb|S|SS
-- A -> a|C
-- B -> b|C
-- C -> CDE
-- D -> ab|A|B
-- F -> E|A|F|FA
--
eliminateLambdaRules :: [Rule] -- ^ Production rules
                     -> [Rule] -- ^ Production rules without labda rules
eliminateLambdaRules rs = nonNullableRules ++ eliminatedLambdaRules
    where
        nonNullableRules       = filter (\x -> not $ elem x $ nullableRules rs) rs
        nonLambdaNullableRules =  filter (\(_ :-> s) -> s /= lambda) $ nullableRules rules
        eliminatedLambdaRules = nub $ concat [ [ v :-> s' | s' <- tail $ pset s ] | (v :-> s) <- nonLambdaNullableRules ]



-- >>> printRules $ eliminateUnitRules $ eliminateLambdaRules rules
-- S -> aAa|bBb|SS
-- A -> a|CDE
-- B -> b|CDE
-- C -> CDE
-- D -> ab|a|b|CDE
-- F -> FA|a|CDE
--
eliminateUnitRules :: [Rule] -- ^ Production rules
                   -> [Rule] -- ^ Production rules without unit rules
eliminateUnitRules rs = ensemble $ transitiveClosure $ unitRules rs
    where
        ensemble pairs = nub $ concat [ [ a :-> getRhs rule | rule <- getRulesFor rs b, not $ isUnitRule rule ] | (a, b) <- pairs] 


-- >>> printRules $ generatingRules rules
-- S -> λ|SS|aAa|bBb
-- A -> a|C
-- B -> b|C
-- C -> λ
-- D -> ab|A|B
-- F -> λ|FA
--
-- >>> printRules $ generatingRules $ eliminateUnitRules $ eliminateLambdaRules rules
-- A -> a
-- B -> b
-- D -> ab|a|b
-- F -> a|FA
-- S -> aAa|bBb|SS
--
generatingRules :: [Rule] -- ^ Production rules
                -> [Rule] -- ^ List of rules containing only generating variables
generatingRules rs = genericInduction cond base rs
    where
        base                            = filter (isGenertingRule) rs
        cond closure (_ :-> s)          = all (\x -> isTerminal x || hasGeneratingRule closure x) s
        isGenertingRule (_ :-> s)       = all (isTerminal) s
        hasGeneratingRule closure var   = any (\(v :-> _) -> var == v) closure

-- >>> printRules $ reachableRules 'S' rules
-- S -> SS|aAa|bBb|λ
-- A -> a|C
-- B -> b|C
-- C -> λ
-- D -> ab|A|B
-- F -> λ|FA
--
-- >>> printRules $ reachableRules 'S' $ generatingRules $ eliminateUnitRules $ eliminateLambdaRules rules
-- S -> aAa|bBb|SS
-- A -> a
-- B -> b
-- D -> ab|a|b
-- F -> a|FA
--
reachableRules :: Char   -- ^ Initial variable
               -> [Rule] -- ^ Production rules
               -> [Rule] -- ^ List of rules containing only reachable variables
reachableRules start rs = genericInduction cond base rs
    where
        base                    = filter (\(v :-> _) -> v == start) rs
        cond closure (_ :-> s)  = all (\x -> isTerminal x || hasReachableRule closure x) s
        hasReachableRule closure var    = any (\(v :-> _) -> var == v) closure


