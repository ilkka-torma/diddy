import diddy
d = diddy.Diddy()

if __name__ == "__main__":

    '''d.run("""
    %alphabet 0 1
    %topology CR
    
    %SFT idcode Ao let c u v := v = 1 & u ~ v in
    (Ed[o1] c o d) & (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q))
    --%SFT test Ao ((has o NW) -> o = 1) & (!(has o NW) -> o = 0)

    --%calculate_forbidden_patterns idcode
    --%show_forbidden_patterns idcode
    
    --%minimum_density idcode (0,3)

    %tiler x_size=9 y_size=3 @x_periodic @y_periodic
     idcode
    --%tiler gridmoves=[[1 0] [-1/2 1/2]]
    --  node_offsets={big:[0 0] small:[1/2 0]}
    --  idcode
      
    """)'''
    
    d.run("""
    -- Cundy Rollet 4.8^2, see Wikipedia
    -- Euclidean tilings by convex regular polygons
    %alphabet 0 1
    %nodes big small
    %topology
    N (0,0,big) (0,1,small);
    NE (0,0,big) (1,1,big);
    E (0,0,big) (0,0,small);
    SE (0,0,big) (0,-1,big);
    S (0,0,big) (-1,-1,small);
    SW (0,0,big) (-1,-1,big);
    W (0,0,big) (-1,0,small);
    NW (0,0,big) (0,1,big);
    N (0,0,small) (1,1,big);
    E (0,0,small) (1,0,big);
    S (0,0,small) (0,-1,big);
    W (0,0,small) (0,0,big)
    %SFT idcode Ao let c u v := v = 1 & u ~ v in
    (Ed[o1] c o d) & (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q))
    %SFT idcode2 Ao let c u v := v = 1 & u ~ v in
    (Ed[o1] c o d) & (Ap[o4] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q))
    %contains idcode2 idcode
    %contains idcode idcode2
    --%SFT test Ao ((has o NW) -> o = 1) & (!(has o NW) -> o = 0)

    --%calculate_forbidden_patterns idcode
    --%show_forbidden_patterns idcode
    --%minimum_density @verbose idcode (0,4)

    --%density_lower_bound @verbose idcode (0,1) (1,0); (0,0,big) (0,0,small) (1,0,big) (1,0,small) (0,1,big) (0,-1,big)

    --%tiler gridmoves=[[1 0] [-1/2 1/2]]
    --  node_offsets={big:[0 0] small:[1/2 0]}
    --  x_size=20 y_size=20
    --  idcode
      
    """)
