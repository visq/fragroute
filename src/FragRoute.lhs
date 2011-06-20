Modelling Fragment Switches in the TTSoC
========================================

> module FragRoute where

Solving
-------

`FragOpt.lhs <FragOpt.html>`_

Modelling Language: `Solve.lhs <Solve.html>`_

Drawing
-------
`FragDraw.lhs <FragDraw.html>`_

The Basics
----------
This is a literal haskell file. Just copy it into a file named ``FragRoute.lhs``,
and you are ready to use the code.

As always, we start with some basic imports:

> import Data.Maybe
> import Data.List
> import Data.Array

The NOC of the TTSoC is a regular M x N mesh, with cores connected on
all four sides. The mesh is composed of fragment switches, which
have inputs and outputs in all four directions.

> data Dir = N | W | S | E deriving (Eq,Ord,Show,Read,Enum,Bounded)
> toRad :: Dir -> Double
> toRad dir = pi / 2 * (fromIntegral (fromEnum dir)) + pi/2

Here is a picture of a 3 x 2 mesh, with routes connecting a few of
the cores: 

.. image:: mesh.png

A fragment switch assigns each input to one output. This mapping has
to be bijective, i.e., no two inputs are allowed to map to the same
output. In our model, we also allow inputs to be inactive. In this
case, the input is not used, and the output direction for this input
is irrelevant.

For simplicity, we model the configuration of one switch as a
list of input/output direction pairs.

> type SwitchConfig = [(Dir,Dir)]
> type Switch   = (Int,Int)

One configuration assigns connections to each fragment switch.

> type MeshConfig = Array Switch SwitchConfig

> dimensions :: MeshConfig -> (Int,Int)
> dimensions meshArray = (\(x,y) -> (x+1,y+1)) $ snd (bounds meshArray)

> meshBounds :: (Int,Int) -> ((Int,Int),(Int,Int))
> meshBounds (cols,rows) = ((0,0),(cols-1,rows-1))

One of the simplest configurations for a NxM mesh just connects neighbours
from east and west, and from north and south in each switch:

> gridConfig :: (Int,Int) -> MeshConfig
> gridConfig dim = array (meshBounds dim)
>                  [ ( pos , [(N,S),(S,N),(W,E),(E,W)] ) | pos <- range (meshBounds dim) ]

The configuration of a switch is valid if the list of inputs and
outputs is unique, and no route maps the input to itself.

> validSwitchConfig :: [(Dir,Dir)] -> Bool
> validSwitchConfig config = let (ins,outs) = unzip config
>                            in noneRepeated ins && noneRepeated outs && all (uncurry (/=)) config
>                            where noneRepeated xs = xs == nub xs

> validConfig :: MeshConfig -> Bool
> validConfig mesh = all validSwitchConfig (elems mesh)

Cores are connected to the NoC at all four sides; the following function produces a list
of switches, and the side where the core is attached to the switch.

> type Core = (Switch,Dir)

> attachedCores :: (Int,Int) -> [Core]
> attachedCores (cols,rows) = coreList W [0] [0..rows-1] ++ coreList E [cols-1] [0..rows-1] ++
>                             coreList N [0..cols-1] [0] ++ coreList S [0..cols-1] [rows-1]
>  where
>    coreList attachedDir xs ys = [ ( (x,y), attachedDir ) | x <- xs, y <- ys ]

> toCoreId :: (Switch,Dir) -> Integer
> toCoreId (s,dir)   = fromIntegral $ ( (if dir `elem` [N,S] then fst else snd) s * 4 + fromEnum dir + 1 )

> fromCoreId :: Integer -> Maybe (Dir, Int)
> fromCoreId n | n > 0     = let (ix,d) = divMod (fromIntegral n - 1) 4 in Just (toEnum d, ix)
>              | otherwise = Nothing

The neighbour of a switch for a given output direction is given by the following
equations:

> neighbour :: Switch -> Dir -> (Switch,Dir)
> neighbour (x,y) dir = case dir of
>   N -> ( (x,y-1), S)
>   W -> ( (x-1,y), E)
>   S -> ( (x,y+1), N)
>   E -> ( (x+1,y), W)

> meshNeighbour :: ((Int,Int),(Int,Int)) -> Switch -> Dir -> Maybe (Switch, Dir)
> meshNeighbour bounds switch dir
>   | inRange bounds switch' = Just next
>   | otherwise = Nothing
>   where next@(switch',_) = neighbour switch dir

To find all possible routes for a given, valid configuration of a mesh, we
follow the routes starting from each core.

> routes :: MeshConfig -> [ ( (Core,Core) , [Switch] ) ]
> routes mesh = mapMaybe startRoute (attachedCores (dimensions mesh))
>   where
>     startRoute core = buildRoute core [] core
>     buildRoute start route (switch,dir) =
>       case lookup dir (mesh ! switch) of
>         Nothing   -> Nothing
>         Just outDir ->
>           case meshNeighbour (bounds mesh) switch outDir of
>             Just next -> buildRoute start (switch:route) next
>             Nothing   -> Just $ ( (start,(switch,outDir)) , reverse (switch:route) )

To pragmatic goal of playing around with fragment switches is to an optimal set of routes
for a fairly small (3x2) NoC actually in use in the TTSoC architecture. To this end,
we will formulate an SAT/ILP problem. The input space will consist of integer variables of type
PortVar; for the full solver implementation, continue with `FragOpt.lhs <FragOpt.html>`_.

> data PortVar = PortVar { var_phase :: Int, var_switch :: Switch, var_input :: Bool, var_dir :: Dir }
>            deriving (Eq,Ord,Show,Read)

Finally, we also want to illustrate meshes and routes programatically, using the fabolous
diagrams package. If you are interested in the drawing stuff, have a look at `FragDraw.lhs <FragDraw.html>`_.
