open tactic

namespace list
example : length ([] : list unit) = 0 :=
begin dunfold length, reflexivity end
end list
