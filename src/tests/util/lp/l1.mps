*SOURCE Chvatal, page 135(b)
NAME          l1
ROWS
 N  Z
 L  R1
 L  R2
 L  R3
 L  R4
COLUMNS
    X1          Z 3 R1 1 R2 1 R3 1 R4 1
    X2          Z 1 R1 4 R2 3 R3 2 R4 3
    X3          Z 4 R1 3 R2 -1 R3 3 R4 1
    X4          Z 2 R1 3 R2 1 R3 2 R4 1

RHS
    RHS1      R1                2
    RHS1      R2                -2
    RHS1      R3                3
    RHS1      R4                -3
BOUNDS
 FR BND1      X1
 FR BND1      X2
 LO BND1      X3                0
 LO BND1      X4                0
ENDATA
