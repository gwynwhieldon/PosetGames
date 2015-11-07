-- Copyright 2015: Gwyn Whieldon
-- You may redistribute this file under the terms of the GNU General Public
-- License as published by the Free Software Foundation, either version 2
-- of the License, or any later version.

------------------------------------------
------------------------------------------
-- Header
------------------------------------------
------------------------------------------

newPackage select((
    "PosetGames",
        Version => "0.0.2",
        Date => "01. November 2015",
        Authors => {
            {Name => "Gwyn Whieldon", Email => "whieldon@hood.edu", HomePage => "http://www.hood.edu/Academics/Departments/Mathematics/Faculty/Gwyneth-Whieldon.html"}
        },
        Headline => "Package for combinatorial games on posets",
        Configuration => {
            "DefaultPDFViewer" => "open", -- "open" for Macs and "evince" for Linux
            "DefaultPrecompute" => true,
            "DefaultSuppressLabels" => true
            },
        DebuggingMode => false,
        PackageExports => {
            "Posets"
            }
        ), x -> x =!= null)

-- Load configurations
posets'PDFViewer = if instance((options Posets).Configuration#"DefaultPDFViewer", String) then (options Posets).Configuration#"DefaultPDFViewer" else "open";
posets'Precompute = if instance((options Posets).Configuration#"DefaultPrecompute", Boolean) then (options Posets).Configuration#"DefaultPrecompute" else true;
posets'SuppressLabels = if instance((options Posets).Configuration#"DefaultSuppressLabels", Boolean) then (options Posets).Configuration#"DefaultSuppressLabels" else true;

export {
    "allMoves",
    "posetgame",
    "spragueGrundy",
    "rankedSpragueGrundy",
    "losingBoards",
    "optimalMove",
    "posetBoard",
    "drawLosingBoards"
    }

------------------------------------------
------------------------------------------
-- Methods
------------------------------------------
------------------------------------------

filterComplement = method()
filterComplement(Poset,List) := (P,L) -> (
    F := filter(P,L);
    P - F
)

posetBoard = method()
posetBoard(Poset,List) := (P,L) -> (
    F := orderIdeal(P,L);
    subposet(P,F)
)


allMoves = method()
allMoves(Poset,List) := (P,L) -> (
    Q := subposet(P,orderIdeal(P,L));
    minElems := minimalElements Q;
    nonMinElements := select(Q.GroundSet, q->not member(q,minElems));
    apply(nonMinElements,q->sort maximalElements(filterComplement(Q,{q})))
)


allMovePairs = method()
allMovePairs(Poset,List) := (P,L) -> (
    apply(allMoves(P,L), l-> {L,{l}})
)

posetgame = method()
posetgame(Poset) := P -> (
    maxElems := maximalElements P;
    hashPairs := unique flatten apply(maxElems,L -> allMovePairs(P,{L}));
    H := hashTable(join,hashPairs);
    V := sort unique flatten values H;
    K := join(keys H,{minimalElements P});
    Vnew := V;
    Hnew := {};
    for i from 0 to #P.GroundSet do (
        Hnew = hashTable(join,flatten apply(Vnew,v->allMovePairs(P,v)));
        H = merge(H,Hnew,join);
        K = join(keys H,{minimalElements P});
        V = sort unique flatten values H;
        Vnew = select(V, i-> not member(i,K));
        if #Vnew == 0 then break H;
        );
    H
)



spragueGrundy = method()
spragueGrundy(Poset) := P -> (
    C := posetgame(P);
    dummyC := new MutableHashTable from C;
    SG := hashTable(apply(minimalElements P, i-> {i}=>0));
    newKeySet := {};
    kVals := {};
    indx := {};
    SGadd := {};
    while (#(keys dummyC) != 0) do(
        newKeySet = select(keys dummyC, k-> all(C#k, v-> member(v,keys SG)));
        for K in newKeySet do (
                kVals = apply(C#K, k-> SG#k);
                indx = toList(0..#kVals);
                SGadd = hashTable({K=>position(indx,i-> not member(i,kVals))});
                SG = merge(SG,SGadd,join);
                remove(dummyC,K);
        );
    );
    SG
);

spragueGrundy(Poset,HashTable) := (P,G) -> (
    dummyC := new MutableHashTable from G;
    SG := hashTable(apply(minimalElements P, i-> {i}=>0));
    newKeySet := {};
    kVals := {};
    indx := {};
    SGadd := {};
    while (#(keys dummyC) != 0) do(
        newKeySet = select(keys dummyC, k-> all(G#k, v-> member(v,keys SG)));
        for K in newKeySet do (
                kVals = apply(G#K, k-> SG#k);
                indx = toList(0..#kVals);
                SGadd = hashTable({K=>position(indx,i-> not member(i,kVals))});
                SG = merge(SG,SGadd,join);
                remove(dummyC,K);
        );
    );
    SG
);

rankedSpragueGrundy = method()
rankedSpragueGrundy(Poset) := P -> (
    C := posetgame(P);
    dummyC := new MutableHashTable from C;
    SG := hashTable(apply(minimalElements P, i-> {i}=>0));
    levels := {apply(keys SG, k-> k => SG#k)};
    newKeySet := {};
    kVals := {};
    indx := {};
    SGadd := {};
    while (#(keys dummyC) != 0) do(
        newKeySet = select(keys dummyC, k-> all(C#k, v-> member(v,keys SG)));
        SGadd = hashTable{};
        for K in newKeySet do (
                kVals = apply(C#K, k-> SG#k);
                indx = toList(0..#kVals);
                SGadd = merge(SGadd,hashTable({K=>position(indx,i-> not member(i,kVals))}),join);
                remove(dummyC,K);
        );
        levels = join(levels,{apply(keys SGadd,k-> k=> SGadd#k)});
        SG = merge(SG,SGadd,join);
    );
    {SG,levels}
);

rankedSpragueGrundy(Poset,HashTable) := (P,C) -> (
    dummyC := new MutableHashTable from C;
    SG := hashTable(apply(minimalElements P, i-> {i}=>0));
    levels := {apply(keys SG, k-> k => SG#k)};
    newKeySet := {};
    kVals := {};
    indx := {};
    SGadd := {};
    while (#(keys dummyC) != 0) do(
        newKeySet = select(keys dummyC, k-> all(C#k, v-> member(v,keys SG)));
        SGadd = hashTable{};
        for K in newKeySet do (
                kVals = apply(C#K, k-> SG#k);
                indx = toList(0..#kVals);
                SGadd = merge(SGadd,hashTable({K=>position(indx,i-> not member(i,kVals))}),join);
                remove(dummyC,K);
        );
        levels = join(levels,{apply(keys SGadd,k-> k=> SGadd#k)});
        SG = merge(SG,SGadd,join);
    );
    {SG,levels}
);

losingBoards = method();
losingBoards(Poset) := P -> (
    SG := spragueGrundy(P);
    sort select(keys SG, k-> SG#k===0)
)

losingBoards(Poset,HashTable) := (P,G) -> (
    SG := spragueGrundy(P,G);
    sort select(keys SG, k-> SG#k===0)
)


optimalMove = method();
optimalMove(Poset,List) := (P,L) -> (
    G := posetgame(P);
    SG := spragueGrundy(P);
    if SG#L === 0 then (
        "No winning move."
    ) else (
        sort select(G#L, k-> SG#k === 0)
    )
)

optimalMove(Poset,HashTable,List) := (P,G,L) -> (
    SG := spragueGrundy(P,G);
    if SG#L === 0 then (
        "No winning move."
    ) else (
        sort select(G#L, k-> SG#k === 0)
    )
)


outputLosingBoards = method();
outputLosingBoards(Poset,List,String) := String => (P,L,name) -> (
    fn := openOut name;
    fn << "\\documentclass[8pt]{amsart}"<< endl;
    fn << "\\usepackage[margin=1.25in, headheight=14pt]{geometry}" << endl;
    fn << "\\usepackage{amsmath,tikz}" << endl;
    fn << "\\begin{document}" << endl;
    fn << "\\title{Losing Poset Boards for Poset P}" << endl;
    fn << "\\maketitle" << endl << endl;
    fn << "Original Poset:" << endl << endl;
    fn << texPoset(P,SuppressLabels=>false) << endl;
    fn << "Losing Boards:" << endl << endl;
    for M in L do (
	fn << texPoset(M,SuppressLabels=>false) << endl;
	fn << "\\vspace{50pt}" << endl << endl;
	);
    fn << "\\end{document}" << endl;
    close fn;
    get name
    )

outputLosingBoards(Poset,List,String) := String => (P,L,name) -> (
    fn := openOut name;
    fn << "\\documentclass[8pt]{amsart}"<< endl;
    fn << "\\usepackage[margin=1.25in, headheight=14pt]{geometry}" << endl;
    fn << "\\usepackage{amsmath,tikz}" << endl;
    fn << "\\begin{document}" << endl;
    fn << "\\title{Losing Poset Boards for Poset P}" << endl;
    fn << "\\maketitle" << endl << endl;
    fn << "Original Poset:" << endl << endl;
    fn << texPoset(P,SuppressLabels=>false) << endl;
    fn << "Losing Boards:" << endl << endl;
    for M in L do (
	fn << texPoset(M,SuppressLabels=>false) << endl;
	fn << "\\vspace{50pt}" << endl << endl;
	);
    fn << "\\end{document}" << endl;
    close fn;
    get name
    )

drawLosingBoards = method()
drawLosingBoards(Poset) := (P) -> (
    L := apply(losingBoards(P), l-> posetBoard(P,l));
    name := toString(random(1000,100000));
    outputLosingBoards(P,L, concatenate(name,".tex"));
    run concatenate("pdflatex ", name,".tex 1>/dev/null");
    run concatenate("open "," ",name,".pdf&");
    removeFile(concatenate(name,".log"));
    removeFile(concatenate(name,".aux"));
    removeFile(concatenate(name,".tex")); 
    )

drawLosingBoards(Poset,HashTable) := (P,G) -> (
    L := apply(losingBoards(P,G), l-> posetBoard(P,l));
    name := toString(random(1000,100000));
    outputLosingBoards(P,L, concatenate(name,".tex"));
    run concatenate("pdflatex ", name,".tex 1>/dev/null");
    run concatenate("open "," ",name,".pdf&");
    removeFile(concatenate(name,".log"));
    removeFile(concatenate(name,".aux"));
    removeFile(concatenate(name,".tex")); 
    )



end;