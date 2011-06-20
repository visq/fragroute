> {-# LANGUAGE NoMonomorphismRestriction #-}

Drawing Fragment Switch Routes using diagrams
=============================================
  
> module Main where

> import Control.Monad
> import Data.List
> import Data.Maybe
> import qualified Data.Map as M
> import Data.Ord
> import System.Exit
> import System.Environment (getArgs, withArgs)

> import Diagrams.Prelude
> import Diagrams.Backend.Cairo.CmdLine

Import the definitions for fragment switches

> import FragRoute

We define how to draw a route between an input and an output port:

> drawRoute :: (Show l) => (Dir,Dir) -> l -> Diagram Cairo R2
> drawRoute (start,end) label =
>   eqTriangle # fc red # scale 0.1 # rotate (Rad (angleOfVector routeVec - pi/2)) # translate startPoint
>     `atop`
>   line [ startPoint .+^ (0.3 *^ startVec), startPoint, endPoint, endPoint .+^ (0.3 *^ endVec) ] # lw 0.02
>      `atop`
>   text (show label) # scale 0.25 # translate (circlePoint (toRad start + 2.5 * doffs) .+^ (0.15 *^ startVec))
>   where
>         (startPoint, startVec) = prefixAndCirclePoint (start,(+doffs))
>         (endPoint, endVec) = prefixAndCirclePoint (end,(\x->x-doffs))
>         routeVec = endVec ^-^ startVec
>         prefixAndCirclePoint (dir,offs) = (circlePoint (offs $ toRad dir), circlePoint (toRad dir))
>         doffs = pi/32
>         line = stroke . fromVertices . map (origin .+^) 
>         circlePoint angle = (cos angle, sin angle)
>         angleOfVector (x,y) = atan2 y x

The routine for drawing a fragment switch mesh with attached cores:

> type SwitchLayout label = [ ( (Dir,Dir), label ) ]
> drawMesh :: (Show l) => [[l]] -> [[SwitchLayout l]] -> Diagram Cairo R2
> drawMesh cores@[north,west,south,east] switches =
>            hcatC (nodes north (strutX 1.6))
>            ===
>            (vcatC (nodes west (strutY 1.6)) ||| gridC mesh ||| vcatC (nodes east (strutY 1.6))) # centerX
>            ===
>            hcatC (nodes south (strutX 1.6))
>   where
>     nodes names inter = intersperse inter $ map (\n -> unitSquare `atop` text (show n)) names
>     mesh = map (map drawSwitch) switches
>     drawSwitch = withNodeBounds . foldr atop (circle 1.0) . map (uncurry drawRoute)
>     withNodeBounds = withBounds (circle 1.3 :: Diagram Cairo R2)
>     hcatC  = centerX . hcat . map centerY
>     vcatC  = centerY . vcat . map centerX
>     gridC  = centerY . vcat . map hcatC

> groupBy' :: (Eq b) => (a -> b) -> [a] -> [[a]]
> groupBy' f = groupBy (\a b -> f a == f b)
> sortAndGroup :: (Ord b) => (a -> b) -> [a] -> [[a]]
> sortAndGroup f =  groupBy' f . sortBy (comparing f)

Drawing one phase:

> drawSolution :: (Int,Int) -> Int -> [ (PortVar, Integer) ] -> Diagram Cairo R2
> drawSolution dim phase configuration = drawMesh cores switches
>   where
>     cores@[north,west,south,east] = map (map toCoreId) . sortAndGroup snd $ attachedCores dim
>     grid = map (sortAndGroup (fst . var_switch . fst)) . sortAndGroup (snd . var_switch . fst) $ configuration
>     switches = map (map switchConfig) grid
>     switchConfig switchSolution = mapMaybe routeSpec . groupBy' snd . sortBy sortSpec $ switchSolution
>       where sortSpec = comparing (\(pv,signal) -> (signal, var_input pv))
>             routeSpec ( (pv1,l) : _) | l == 0 = Nothing
>             routeSpec [(pv1,l),(pv2,l2)] | l==l2 = Just ( (var_dir pv2, var_dir pv1) , l )
>             routeSpec [(pvi,_)] | var_input pvi = Nothing
>             routeSpec badSpec = error $ show badSpec ++ " in " ++ show switchSolution

The executable reads a solution produced by `FragOpt.lhs <FragOpt.html>`_, and draws a diagram
for the selected phase (if it exists).

> main :: IO ()
> main = do
>  args <- getArgs
>  inputFile <- case args of
>     [] -> error "Usage: fragdraw -o output.pdf --selection Phase_N input.dat"
>     xs -> return $ last xs
>  mSolution <- liftM read (readFile inputFile)
>  solution <- case mSolution of
>    Nothing -> error $ "No solution found for input file" ++ inputFile
>    Just s  -> return s
>  let dim = let switches = map (var_switch . fst) (M.toList solution)
>            in  (maximum (map fst switches) + 1, maximum (map snd switches) + 1)
>  let solutionsByPhase =  map (filterConfiguration dim) . zip [0..] . groupBy' (var_phase . fst) . M.toList $ solution
>  putStrLn $ "Signals routed in total: " ++ ((show  . length . concat . map (routedSignals dim)) $ solutionsByPhase)
>  putStrLn $ "Rendering Diagram with dimension " ++ show dim
>  withArgs (init args) $ multiMain $ [ ("Phase_"++show i, drawSolution dim i sol) | (i,sol) <- solutionsByPhase ]
>  where
>     filterConfiguration dim solution@(phase,config) = (,) phase $
>          [ portconfig | portconfig <- config, snd portconfig `elem` map fst (routedSignals dim solution) ]
>     routedSignals :: (Int,Int) -> (Int,  [ (PortVar, Integer) ] ) -> [(Integer,Integer)]
>     routedSignals dim (phase,config) =
>          [ (sourceId,toCoreId c) | c@(s,d) <- attachedCores dim
>                                  , sourceId <- maybeToList (lookup (PortVar phase s False d) config)
>                                  , sourceId /= 0 ]

And what does it look like? Here is the visualization of one phase in a 3 x 2 mesh:

.. image:: mesh_11_7.png