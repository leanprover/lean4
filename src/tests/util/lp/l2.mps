NAME          l2 ( from chvatal's book page 135, Problem c. )
ROWS
 N  Z
 L  R1
 L  R2
 E  R3
COLUMNS
    X1        Z   5  R1  3 R2 -5  R3 1
    X2        Z   2  R1  1 R2  4  R3 1
    X3        Z  -3  R1 -4 R2  2  R3 2
    X4        Z   3  R1  2 R2 -3  R3 1
    X5        Z   6  R1  5 R2  2  R3 1
    X6        Z   1  R1  1 R2  3  R3 2
RHS
    RHS1      R1                3
    RHS1      R2                25
    RHS1      R3                4
BOUNDS
 LO BND1      X1                0
 LO BND1      X2                2
 UP BND1      X2               10
 UP BND1      X3                0
 LO BND1      X4                -3
 UP BND1      X4                3
 FR BND1      X5
 FR BND1      X6
ENDATA
