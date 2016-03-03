import data.real
open real

/-
variable {A : Type}
variable [s : linear_ordered_field A]
include s-/
notation `A` := real

example : (-1 :A) * 1 = -1 := by norm_num
example : (-2 :A) * 1 = -2 := by norm_num
example : (-2 :A) * -1 = 2 := by norm_num
example : (-2 :A) * -2 = 4 := by norm_num
example : (1 : A) * 0 = 0 := by norm_num

example : ((1 : A) + 1) * 5 = 6 + 4 := by norm_num

example : (1 : A) = 0 + 1 := by norm_num
example : (1 : A) = 1 + 0 := by norm_num
example : (2 : A) = 1 + 1 := by norm_num
example : (2 : A) = 0 + 2 := by norm_num
example : (3 : A) = 1 + 2 := by norm_num
example : (3 : A) = 2 + 1 := by norm_num
example : (4 : A) = 3 + 1 := by norm_num
example : (4 : A) = 2 + 2 := by norm_num
example : (5 : A) = 4 + 1 := by norm_num
example : (5 : A) = 3 + 2 := by norm_num
example : (5 : A) = 2 + 3 := by norm_num
example : (6 : A) = 0 + 6 := by norm_num
example : (6 : A) = 3 + 3 := by norm_num
example : (6 : A) = 4 + 2 := by norm_num
example : (6 : A) = 5 + 1 := by norm_num
example : (7 : A) = 4 + 3 := by norm_num
example : (7 : A) = 1 + 6 := by norm_num
example : (7 : A) = 6 + 1 := by norm_num
example : 33 = 5 + (28 : A) := by norm_num

example : (12 : A) = 0 + (2 + 3) + 7 := by norm_num
example : (105 : A) = 70 + (33 + 2) := by norm_num
theorem name : (45000000000 : A) = 23000000000 + 22000000000 := by norm_num

example : (0 : A) - 3 = -3 := by norm_num
example : (0 : A) - 2 = -2 := by norm_num
example : (1 : A) - 3 = -2 := by norm_num
example : (1 : A) - 1 = 0 := by norm_num
example : (0 : A) - 3 = -3 := by norm_num
example : (0 : A) - 3 = -3 := by norm_num

example : (12 : A) - 4 - (5 + -2) = 5 := by norm_num
example : (12 : A) - 4 - (5 + -2) - 20 = -15 := by norm_num

example : (0 : A) * 0 = 0 := by norm_num
example : (0 : A) * 1 = 0 := by norm_num
example : (0 : A) * 2 = 0 := by norm_num
example : (2 : A) * 0 = 0 := by norm_num
example : (1 : A) * 0 = 0 := by norm_num
example : (1 : A) * 1 = 1 := by norm_num
example : (2 : A) * 1 = 2 := by norm_num
example : (1 : A) * 2 = 2 := by norm_num
example : (2 : A) * 2 = 4 := by norm_num
example : (3 : A) * 2 = 6 := by norm_num
example : (2 : A) * 3 = 6 := by norm_num
example : (4 : A) * 1 = 4 := by norm_num
example : (1 : A) * 4 = 4 := by norm_num
example : (3 : A) * 3 = 9 := by norm_num
example : (3 : A) * 4 = 12 := by norm_num
example : (4 : A) * 4 = 16 := by norm_num
example : (11 : A) * 2 = 22 := by norm_num
example : (15 : A) * 6 = 90 := by norm_num
example : (123456 : A) * 123456 = 15241383936 := by norm_num

example : (4 : A) / 2 = 2 := by norm_num
example : (4 : A) / 1 = 4 := by norm_num
example : (4 : A) / 3 = 4 / 3 := by norm_num
example : (50 : A) / 5 = 10 := by norm_num
example : (1056 : A) / 1 = 1056 := by norm_num
example : (6 : A) / 4 = 3/2 := by norm_num
example : (0 : A) / 3 = 0 := by norm_num
--example : (3 : A) / 0 = 0 := by norm_num -- this should fail
example : (9 * 9 * 9) * (12 : A) / 27 = 81 * (2 + 2) := by norm_num
example : (-2 : A) * 4 / 3 = -8 / 3 := by norm_num
example : - (-4 / 3) = 1 / (3 / (4 : A)) := by norm_num

-- auto gen tests
example : ((25 * (1 / 1)) + (30 - 16)) = (39 : A) := by norm_num
example : ((19 * (- 2 - 3)) / 6) = (-95/6 : A) := by norm_num
example : - (3 * 28) = (-84 : A) := by norm_num
example : - - (16 / ((11 / (- - (6 * 19) + 12)) * 21)) = (96/11 : A) := by norm_num
example : (- (- 21 + 24) - - (- - (28 + (- 21 / - (16 / ((1 * 26) * ((0 * - 11) + 13))))) * 21)) = (79209/8 : A) := by norm_num
example : (27 * (((16 + - (12 + 4)) + (22 - - 19)) - 23)) = (486 : A) := by norm_num
example : - (13 * (- 30 / ((7 / 24) + - 7))) = (-9360/161 : A) := by norm_num
example : - (0 + 20) = (-20 : A) := by norm_num
example : (- 2 - (27 + (((2 / 14) - (7 + 21)) + (16 - - - 14)))) = (-22/7 : A) := by norm_num
example : (25 + ((8 - 2) + 16)) = (47 : A) := by norm_num
example : (- - 26 / 27) = (26/27 : A) := by norm_num
example : ((((16 * (22 / 14)) - 18) / 11) + 30) = (2360/77 : A) := by norm_num
example : (((- 28 * 28) / (29 - 24)) * 24) = (-18816/5 : A) := by norm_num
example : ((- (18 - ((- - (10 + - 2) - - (23 / 5)) / 5)) - (21 * 22)) - (((20 / - ((((19 + 18) + 15) + 3) + - 22)) + 14) / 17)) = (-394571/825 : A) := by norm_num
example : ((3 + 25) - - 4) = (32 : A) := by norm_num
example : ((1 - 0) - 22) = (-21 : A) := by norm_num
example : (((- (8 / 7) / 14) + 20) + 22) = (2054/49 : A) := by norm_num
example : ((21 / 20) - 29) = (-559/20 : A) := by norm_num
example : - - 20 = (20 : A) := by norm_num
example : (24 - (- 9 / 4)) = (105/4 : A) := by norm_num
example : (((7 / ((23 * 19) + (27 * 10))) - ((28 - - 15) * 24)) + (9 / - (10 * - 3))) = (-1042007/1010 : A) := by norm_num
example : (26 - (- 29 + (12 / 25))) = (1363/25 : A) := by norm_num
example : ((11 * 27) / (4 - 5)) = (-297 : A) := by norm_num
example : (24 - (9 + 15)) = (0 : A) := by norm_num
example : (- 9 - - 0) = (-9 : A) := by norm_num
example : (- 10 / (30 + 10)) = (-1/4 : A) := by norm_num
example : (22 - (6 * (28 * - 8))) = (1366 : A) := by norm_num
example : ((- - 2 * (9 * - 3)) + (22 / 30)) = (-799/15 : A) := by norm_num
example : - (26 / ((3 + 7) / - (27 * (12 / - 16)))) = (-1053/20 : A) := by norm_num
example : ((- 29 / 1) + 28) = (-1 : A) := by norm_num
example : ((21 * ((10 - (((17 + 28) - - 0) + 20)) + 26)) + ((17 + - 16) * 7)) = (-602 : A) := by norm_num
example : (((- 5 - ((24 + - - 8) + 3)) + 20) + - 23) = (-43 : A) := by norm_num
example : ((- ((14 - 15) * (14 + 8)) + ((- (18 - 27) - 0) + 12)) - 11) = (32 : A) := by norm_num
example : (((15 / 17) * (26 / 27)) + 28) = (4414/153 : A) := by norm_num
example : (14 - ((- 16 - 3) * - (20 * 19))) = (-7206 : A) := by norm_num
example : (21 - - - (28 - (12 * 11))) = (125 : A) := by norm_num
example : ((0 + (7 + (25 + 8))) * - (11 * 27)) = (-11880 : A) := by norm_num
example : (19 * - 5) = (-95 : A) := by norm_num
example : (29 * - 8) = (-232 : A) := by norm_num
example : ((22 / 9) - 29) = (-239/9 : A) := by norm_num
example : (3 + (19 / 12)) = (55/12 : A) := by norm_num
example : - (13 + 30) = (-43 : A) := by norm_num
example : - - - (((21 * - - ((- 25 - (- (30 - 5) / (- 5 - 5))) / (((6 + ((25 * - 13) + 22)) - 3) / 2))) / (- 3 / 10)) * (- 8 - 0)) = (-308/3 : A) := by norm_num
example : - (2 * - (- 24 * 22)) = (-1056 : A) := by norm_num
example : - - (((28 / - ((- 13 * - 5) / - (((7 - 30) / 16) + 6))) * 0) - 24) = (-24 : A) := by norm_num
example : ((13 + 24) - (27 / (21 * 13))) = (3358/91 : A) := by norm_num
example : ((3 / - 21) * 25) = (-25/7 : A) := by norm_num
example : (17 - (29 - 18)) = (6 : A) := by norm_num
example : ((28 / 20) * 15) = (21 : A) := by norm_num
example : ((((26 * (- (23 - 13) - 3)) / 20) / (14 - (10 + 20))) / ((16 / 6) / (16 * - (3 / 28)))) = (-1521/2240 : A) := by norm_num

example : (46 / (- ((- 17 * 28) - 77) + 87)) = (23/320 : A) := by norm_num
example : (73 * - (67 - (74 * - - 11))) = (54531 : A) := by norm_num
example : ((8 * (25 / 9)) + 59) = (731/9 : A) := by norm_num
example : - ((59 + 85) * - 70) = (10080 : A) := by norm_num
example : (66 + (70 * 58)) = (4126 : A) := by norm_num
example : (- - 49 * 0) = (0 : A) := by norm_num
example : ((- 78 - 69) * 9) = (-1323 : A) := by norm_num
example : - - (7 - - (50 * 79)) = (3957 : A) := by norm_num
example : - (85 * (((4 * 93) * 19) * - 31)) = (18624180 : A) := by norm_num
example : (21 + (- 5 / ((74 * 85) / 45))) = (26373/1258 : A) := by norm_num
example : (42 - ((27 + 64) + 26)) = (-75 : A) := by norm_num
example : (- ((38 - - 17) + 86) - (74 + 58)) = (-273 : A) := by norm_num
example : ((29 * - (75 + - 68)) + (- 41 / 28)) = (-5725/28 : A) := by norm_num
example : (- - (40 - 11) - (68 * 86)) = (-5819 : A) := by norm_num
example : (6 + ((65 - 14) + - 89)) = (-32 : A) := by norm_num
example : (97 * - (29 * 35)) = (-98455 : A) := by norm_num
example : - (66 / 33) = (-2 : A) := by norm_num
example : - ((94 * 89) + (79 - (23 - (((- 1 / 55) + 95) * (28 - (54 / - - - 22)))))) = (-1369070/121 : A) := by norm_num
example : (- 23 + 61) = (38 : A) := by norm_num
example : - (93 / 69) = (-31/23 : A) := by norm_num
example : (- - ((68 / (39 + (((45 * - (59 - (37 + 35))) / (53 - 75)) - - (100 + - (50 / (- 30 - 59)))))) - (69 - (23 * 30))) / (57 + 17)) = (137496481/16368578 : A) := by norm_num
example : (- 19 * - - (75 * - - 41)) = (-58425 : A) := by norm_num
example : ((3 / ((- 28 * 45) * (19 + ((- (- 88 - (- (- 1 + 90) + 8)) + 87) * 48)))) + 1) = (1903019/1903020 : A) := by norm_num
example : ((- - (28 + 48) / 75) + ((- 59 - 14) - 0)) = (-5399/75 : A) := by norm_num
example : (- ((- (((66 - 86) - 36) / 94) - 3) / - - (77 / (56 - - - 79))) + 87) = (312254/3619 : A) := by norm_num
