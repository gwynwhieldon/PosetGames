needsPackage("PosetGames")
n = 72
Q = divisorPoset(n)
G = posetgame(Q)
SG = spragueGrundy(Q,G)
drawLosingBoards(Q,G)