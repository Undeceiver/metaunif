-- These are just hand-wavey tests, to be done in the console. This module is not precise enough to be worth (we think) fully automated complete tests. These are just to see that things look right at a high level.

let g1 = do {cgid <- newEqDGSONode "G"; cfid <- newEqDGSONode "F"; fid <- newEqDGSONode "f"; newEqDGSOEdge cgid [fid,fid] cfid; gid <- newEqDGSONode "g"; s1y <- newEqDGFONode "s1 y"; s1z <- newEqDGFONode "s1 z"; s1x <- newEqDGFONode "s1 x"; gs1yz <- newAnonEqDGFOEdge gid [s1y,s1z]; newEqDGFOEdge cfid [gs1yz] s1x}

let g2 = do {g1; let {s1y = relbwEqDGFoId "s1 y"; g = relbwEqDGSoId "g"}; egs1yzs <- st_searchOutEqDGFOEdges [g] [] s1y; gs1yzs <- traverse eqDGFOEdge_target egs1yzs; let {cf = relbwEqDGSoId "F"}; cfes <- concat <$> (traverse (st_searchOutEqDGFOEdges [cf] []) gs1yzs); traverse deleteEqDGFOEdge cfes; let {f = relbwEqDGSoId "f"}; fgs1yzs <- traverse (\s -> newAnonEqDGFOEdge f [s]) gs1yzs; let {cg = relbwEqDGSoId "G"; s1x = relbwEqDGFoId "s1 x"}; traverse (\s -> newEqDGFOEdge cg [s,s] s1x) fgs1yzs}

let g3 = do {g2; s1w <- newEqDGFONode "s1 w"; let {f = relbwEqDGSoId "f"}; fs1w <- newAnonEqDGFOEdge f [s1w]; return ()}

let g4 = do {g3; let {s1x = relbwEqDGFoId "s1 x"; s1w = relbwEqDGFoId "s1 w"; f = relbwEqDGSoId "f"}; efs1ws <- st_searchOutEqDGFOEdges [f] [] s1w; fs1ws <- traverse eqDGFOEdge_target efs1ws; traverse (\n -> mergeEqDGFONodes n s1x) fs1ws}

let g5_1 = do {g4; let {cg = RelBwId "G"; s1x = RelBwId "s1 x"}; eGs <- st_searchInEqDGFOEdges [cg] [] s1x; eGss <- concat <$> traverse eqDGFOEdge_sources eGs; traverse deleteEqDGFOEdge eGs; pi1 <- newEqDGSONode "pi1"; mergeEqDGSONodes pi1 cg; traverse (mergeEqDGFONodes s1x) eGss}

let g5_2 = do {g5_1; let {f = RelBwId "f"; s1w = RelBwId "s1 w"; s1x = RelBwId "s1 x"}; einfs1xs <- st_searchInEqDGFOEdges [f] [] s1x; einfs1xss <- concat <$> traverse eqDGFOEdge_sources einfs1xs; traverse deleteEqDGFOEdge einfs1xs; traverse (mergeEqDGFONodes s1w) einfs1xss; newEqDGFOEdge f [s1w] s1x}


putStr (runST (show_eqdgraph <$> (snd <$> (runStateT g1 emptyEqDG))))
