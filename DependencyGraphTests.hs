-- These are just hand-wavey tests, to be done in the console. This module is not precise enough to be worth (we think) fully automated complete tests. These are just to see that things look right at a high level.

let g1 = do {cgid <- newEqDGSONode "G"; cfid <- newEqDGSONode "F"; fid <- newEqDGSONode "f"; newEqDGSOEdge "G" ["f","f"] "F"; gid <- newEqDGSONode "g"; s1y <- newEqDGFONode "s1 y"; s1z <- newEqDGFONode "s1 z"; s1x <- newEqDGFONode "s1 x"; (Just gs1yz) <- newAnonEqDGFOEdge "g" ["s1 y","s1 z"]; zoom_on_dgraph (newDGFOEdge cfid [gs1yz] s1x)}
