def my_pre_config1 : smt_pre_config :=
{ default_smt_pre_config . zeta := tt }

def my_pre_config2 : smt_pre_config :=
{ default_smt_pre_config with zeta := tt }
