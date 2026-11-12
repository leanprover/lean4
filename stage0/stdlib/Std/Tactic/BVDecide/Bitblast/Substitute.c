// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.Substitute
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Init.System.ST public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr public import Std.Data.HashMap.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashableKey___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_runST___redArg(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_instHashable___lam__0___boxed(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_literal___override(lean_object*);
uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(uint8_t);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_not___override(lean_object*);
uint8_t l_Std_Tactic_BVDecide_Gate_eval(uint8_t, uint8_t, uint8_t);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_ite___override(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadST___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_instHashableKey___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0;
static lean_once_cell_t l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkGate(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkGate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVLogicalExpr_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__0 = (const lean_object*)&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVLogicalExpr_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__1 = (const lean_object*)&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instBEqOfDecidableEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__1_value)} };
static const lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__2 = (const lean_object*)&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__0, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__0_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__1);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0(lean_object* v_x_9_, lean_object* v_subst_10_, lean_object* v_00_u03c3_11_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2);
v___x_14_ = lean_st_mk_ref(v___x_13_);
lean_inc(v___x_14_);
v___x_15_ = lean_apply_4(v_x_9_, lean_box(0), v_subst_10_, v___x_14_, lean_box(0));
v___x_16_ = lean_st_ref_get(v___x_14_);
lean_dec(v___x_14_);
lean_dec(v___x_16_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___boxed(lean_object* v_x_17_, lean_object* v_subst_18_, lean_object* v_00_u03c3_19_, lean_object* v___y_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0(v_x_17_, v_subst_18_, v_00_u03c3_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg(lean_object* v_subst_22_, lean_object* v_x_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___x_25_; 
v___f_24_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_24_, 0, v_x_23_);
lean_closure_set(v___f_24_, 1, v_subst_22_);
v___x_25_ = l_runST___redArg(v___f_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_subst_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; 
v___f_30_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_30_, 0, v_x_29_);
lean_closure_set(v___f_30_, 1, v_subst_28_);
v___x_31_ = l_runST___redArg(v___f_30_);
return v___x_31_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__1(void){
_start:
{
lean_object* v___x_33_; lean_object* v___f_34_; 
v___x_33_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_Cache_instDecidableEqKey___boxed), 2, 0);
v___f_34_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_34_, 0, v___x_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg(lean_object* v_inst_35_, lean_object* v_w_36_, lean_object* v_expr_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
switch(lean_obj_tag(v_expr_37_))
{
case 0:
{
lean_object* v_idx_41_; lean_object* v_bvAtom_42_; lean_object* v___x_43_; 
v_idx_41_ = lean_ctor_get(v_expr_37_, 1);
lean_inc_n(v_idx_41_, 2);
lean_dec_ref_known(v_expr_37_, 2);
v_bvAtom_42_ = lean_ctor_get(v_inst_35_, 0);
lean_inc_ref(v_bvAtom_42_);
lean_inc(v_w_36_);
lean_inc(v_a_38_);
v___x_43_ = lean_apply_3(v_bvAtom_42_, v_a_38_, v_w_36_, v_idx_41_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v___x_44_; 
lean_dec_ref(v_inst_35_);
v___x_44_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v_w_36_, v_idx_41_);
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_46_; 
lean_dec(v_idx_41_);
v_val_45_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___x_43_, 1);
v___x_46_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_val_45_, v_a_38_, v_a_39_);
return v___x_46_;
}
}
case 1:
{
lean_object* v_val_47_; lean_object* v___x_48_; 
lean_dec_ref(v_inst_35_);
v_val_47_ = lean_ctor_get(v_expr_37_, 1);
lean_inc(v_val_47_);
lean_dec_ref_known(v_expr_37_, 2);
v___x_48_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v_val_47_);
return v___x_48_;
}
case 2:
{
lean_object* v_w_49_; lean_object* v_start_50_; lean_object* v_expr_51_; lean_object* v___x_52_; 
v_w_49_ = lean_ctor_get(v_expr_37_, 0);
lean_inc_n(v_w_49_, 2);
v_start_50_ = lean_ctor_get(v_expr_37_, 1);
lean_inc(v_start_50_);
v_expr_51_ = lean_ctor_get(v_expr_37_, 3);
lean_inc_ref(v_expr_51_);
lean_dec_ref_known(v_expr_37_, 4);
v___x_52_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_49_, v_expr_51_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_52_) == 1)
{
lean_object* v_val_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_w_49_);
v_val_53_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_val_53_);
lean_dec_ref_known(v___x_52_, 2);
v___x_54_ = l_BitVec_extractLsb_x27___redArg(v_start_50_, v_w_36_, v_val_53_);
lean_dec(v_val_53_);
lean_dec(v_start_50_);
v___x_55_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(v_w_49_, v_start_50_, v_w_36_, v___x_52_);
return v___x_56_;
}
}
case 3:
{
lean_object* v_lhs_57_; uint8_t v_op_58_; lean_object* v_rhs_59_; lean_object* v_lhs_61_; lean_object* v_rhs_62_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_lhs_57_ = lean_ctor_get(v_expr_37_, 1);
lean_inc_ref(v_lhs_57_);
v_op_58_ = lean_ctor_get_uint8(v_expr_37_, sizeof(void*)*3 + 8);
v_rhs_59_ = lean_ctor_get(v_expr_37_, 2);
lean_inc_ref(v_rhs_59_);
lean_dec_ref_known(v_expr_37_, 3);
lean_inc_n(v_w_36_, 2);
lean_inc_ref(v_inst_35_);
v___x_64_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_lhs_57_, v_a_38_, v_a_39_);
v___x_65_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_rhs_59_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_64_) == 1)
{
if (lean_obj_tag(v___x_65_) == 1)
{
lean_object* v_val_66_; lean_object* v_val_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_val_66_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_val_66_);
lean_dec_ref_known(v___x_64_, 2);
v_val_67_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_val_67_);
lean_dec_ref_known(v___x_65_, 2);
v___x_68_ = l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_36_, v_op_58_, v_val_66_, v_val_67_);
lean_dec(v_val_67_);
lean_dec(v_val_66_);
v___x_69_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_71_; 
v_val_70_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_val_70_);
lean_dec_ref_known(v___x_64_, 2);
lean_inc(v_w_36_);
v___x_71_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v_val_70_);
v_lhs_61_ = v___x_71_;
v_rhs_62_ = v___x_65_;
goto v___jp_60_;
}
}
else
{
v_lhs_61_ = v___x_64_;
v_rhs_62_ = v___x_65_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_w_36_, v_lhs_61_, v_op_58_, v_rhs_62_);
return v___x_63_;
}
}
case 4:
{
lean_object* v_op_72_; lean_object* v_operand_73_; lean_object* v___x_74_; 
v_op_72_ = lean_ctor_get(v_expr_37_, 1);
lean_inc(v_op_72_);
v_operand_73_ = lean_ctor_get(v_expr_37_, 2);
lean_inc_ref(v_operand_73_);
lean_dec_ref_known(v_expr_37_, 3);
lean_inc(v_w_36_);
v___x_74_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_operand_73_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_74_) == 1)
{
lean_object* v_val_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_val_75_ = lean_ctor_get(v___x_74_, 1);
lean_inc(v_val_75_);
lean_dec_ref_known(v___x_74_, 2);
lean_inc(v_w_36_);
v___x_76_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_36_, v_op_72_, v_val_75_);
lean_dec(v_op_72_);
v___x_77_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_w_36_, v_op_72_, v___x_74_);
return v___x_78_;
}
}
case 5:
{
lean_object* v_l_79_; lean_object* v_r_80_; lean_object* v_lhs_81_; lean_object* v_rhs_82_; lean_object* v_lhs_84_; lean_object* v_rhs_85_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_l_79_ = lean_ctor_get(v_expr_37_, 0);
lean_inc_n(v_l_79_, 2);
v_r_80_ = lean_ctor_get(v_expr_37_, 1);
lean_inc_n(v_r_80_, 2);
v_lhs_81_ = lean_ctor_get(v_expr_37_, 3);
lean_inc_ref(v_lhs_81_);
v_rhs_82_ = lean_ctor_get(v_expr_37_, 4);
lean_inc_ref(v_rhs_82_);
lean_dec_ref_known(v_expr_37_, 5);
lean_inc_ref(v_inst_35_);
v___x_87_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_l_79_, v_lhs_81_, v_a_38_, v_a_39_);
v___x_88_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_r_80_, v_rhs_82_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_87_) == 1)
{
if (lean_obj_tag(v___x_88_) == 1)
{
lean_object* v_val_89_; lean_object* v_val_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_l_79_);
v_val_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_val_89_);
lean_dec_ref_known(v___x_87_, 2);
v_val_90_ = lean_ctor_get(v___x_88_, 1);
lean_inc(v_val_90_);
lean_dec_ref_known(v___x_88_, 2);
v___x_91_ = l_BitVec_append___redArg(v_r_80_, v_val_89_, v_val_90_);
lean_dec(v_val_90_);
lean_dec(v_val_89_);
lean_dec(v_r_80_);
v___x_92_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_94_; 
v_val_93_ = lean_ctor_get(v___x_87_, 1);
lean_inc(v_val_93_);
lean_dec_ref_known(v___x_87_, 2);
lean_inc(v_l_79_);
v___x_94_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_l_79_, v_val_93_);
v_lhs_84_ = v___x_94_;
v_rhs_85_ = v___x_88_;
goto v___jp_83_;
}
}
else
{
v_lhs_84_ = v___x_87_;
v_rhs_85_ = v___x_88_;
goto v___jp_83_;
}
v___jp_83_:
{
lean_object* v___x_86_; 
v___x_86_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_l_79_, v_r_80_, v_w_36_, v_lhs_84_, v_rhs_85_);
return v___x_86_;
}
}
case 6:
{
lean_object* v_w_95_; lean_object* v_n_96_; lean_object* v_expr_97_; lean_object* v___x_98_; 
v_w_95_ = lean_ctor_get(v_expr_37_, 0);
lean_inc_n(v_w_95_, 2);
v_n_96_ = lean_ctor_get(v_expr_37_, 2);
lean_inc(v_n_96_);
v_expr_97_ = lean_ctor_get(v_expr_37_, 3);
lean_inc_ref(v_expr_97_);
lean_dec_ref_known(v_expr_37_, 4);
v___x_98_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_95_, v_expr_97_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_98_) == 1)
{
lean_object* v_val_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_val_99_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_98_, 2);
v___x_100_ = l_BitVec_replicate(v_w_95_, v_n_96_, v_val_99_);
lean_dec(v_val_99_);
lean_dec(v_n_96_);
lean_dec(v_w_95_);
v___x_101_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_w_95_, v_w_36_, v_n_96_, v___x_98_);
return v___x_102_;
}
}
case 7:
{
lean_object* v_n_103_; lean_object* v_lhs_104_; lean_object* v_rhs_105_; lean_object* v_lhs_107_; lean_object* v_rhs_108_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_n_103_ = lean_ctor_get(v_expr_37_, 1);
lean_inc_n(v_n_103_, 2);
v_lhs_104_ = lean_ctor_get(v_expr_37_, 2);
lean_inc_ref(v_lhs_104_);
v_rhs_105_ = lean_ctor_get(v_expr_37_, 3);
lean_inc_ref(v_rhs_105_);
lean_dec_ref_known(v_expr_37_, 4);
lean_inc(v_w_36_);
lean_inc_ref(v_inst_35_);
v___x_110_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_lhs_104_, v_a_38_, v_a_39_);
v___x_111_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_n_103_, v_rhs_105_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_110_) == 1)
{
if (lean_obj_tag(v___x_111_) == 1)
{
lean_object* v_val_112_; lean_object* v_val_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_n_103_);
v_val_112_ = lean_ctor_get(v___x_110_, 1);
lean_inc(v_val_112_);
lean_dec_ref_known(v___x_110_, 2);
v_val_113_ = lean_ctor_get(v___x_111_, 1);
lean_inc(v_val_113_);
lean_dec_ref_known(v___x_111_, 2);
v___x_114_ = l_BitVec_shiftLeft(v_w_36_, v_val_112_, v_val_113_);
lean_dec(v_val_113_);
lean_dec(v_val_112_);
v___x_115_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; 
v_val_116_ = lean_ctor_get(v___x_110_, 1);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_110_, 2);
lean_inc(v_w_36_);
v___x_117_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v_val_116_);
v_lhs_107_ = v___x_117_;
v_rhs_108_ = v___x_111_;
goto v___jp_106_;
}
}
else
{
v_lhs_107_ = v___x_110_;
v_rhs_108_ = v___x_111_;
goto v___jp_106_;
}
v___jp_106_:
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(v_w_36_, v_n_103_, v_lhs_107_, v_rhs_108_);
return v___x_109_;
}
}
case 8:
{
lean_object* v_n_118_; lean_object* v_lhs_119_; lean_object* v_rhs_120_; lean_object* v_lhs_122_; lean_object* v_rhs_123_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_n_118_ = lean_ctor_get(v_expr_37_, 1);
lean_inc_n(v_n_118_, 2);
v_lhs_119_ = lean_ctor_get(v_expr_37_, 2);
lean_inc_ref(v_lhs_119_);
v_rhs_120_ = lean_ctor_get(v_expr_37_, 3);
lean_inc_ref(v_rhs_120_);
lean_dec_ref_known(v_expr_37_, 4);
lean_inc(v_w_36_);
lean_inc_ref(v_inst_35_);
v___x_125_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_lhs_119_, v_a_38_, v_a_39_);
v___x_126_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_n_118_, v_rhs_120_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_125_) == 1)
{
if (lean_obj_tag(v___x_126_) == 1)
{
lean_object* v_val_127_; lean_object* v_val_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_n_118_);
v_val_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_val_127_);
lean_dec_ref_known(v___x_125_, 2);
v_val_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc(v_val_128_);
lean_dec_ref_known(v___x_126_, 2);
v___x_129_ = lean_nat_shiftr(v_val_127_, v_val_128_);
lean_dec(v_val_128_);
lean_dec(v_val_127_);
v___x_130_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
v_val_131_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_val_131_);
lean_dec_ref_known(v___x_125_, 2);
lean_inc(v_w_36_);
v___x_132_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v_val_131_);
v_lhs_122_ = v___x_132_;
v_rhs_123_ = v___x_126_;
goto v___jp_121_;
}
}
else
{
v_lhs_122_ = v___x_125_;
v_rhs_123_ = v___x_126_;
goto v___jp_121_;
}
v___jp_121_:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(v_w_36_, v_n_118_, v_lhs_122_, v_rhs_123_);
return v___x_124_;
}
}
default: 
{
lean_object* v_n_133_; lean_object* v_lhs_134_; lean_object* v_rhs_135_; lean_object* v_lhs_137_; lean_object* v_rhs_138_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_n_133_ = lean_ctor_get(v_expr_37_, 1);
lean_inc_n(v_n_133_, 2);
v_lhs_134_ = lean_ctor_get(v_expr_37_, 2);
lean_inc_ref(v_lhs_134_);
v_rhs_135_ = lean_ctor_get(v_expr_37_, 3);
lean_inc_ref(v_rhs_135_);
lean_dec_ref_known(v_expr_37_, 4);
lean_inc(v_w_36_);
lean_inc_ref(v_inst_35_);
v___x_140_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_w_36_, v_lhs_134_, v_a_38_, v_a_39_);
v___x_141_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_35_, v_n_133_, v_rhs_135_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_140_) == 1)
{
if (lean_obj_tag(v___x_141_) == 1)
{
lean_object* v_val_142_; lean_object* v_val_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_n_133_);
v_val_142_ = lean_ctor_get(v___x_140_, 1);
lean_inc(v_val_142_);
lean_dec_ref_known(v___x_140_, 2);
v_val_143_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_val_143_);
lean_dec_ref_known(v___x_141_, 2);
v___x_144_ = l_BitVec_sshiftRight(v_w_36_, v_val_142_, v_val_143_);
lean_dec(v_val_143_);
v___x_145_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_147_; 
v_val_146_ = lean_ctor_get(v___x_140_, 1);
lean_inc(v_val_146_);
lean_dec_ref_known(v___x_140_, 2);
lean_inc(v_w_36_);
v___x_147_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_36_, v_val_146_);
v_lhs_137_ = v___x_147_;
v_rhs_138_ = v___x_141_;
goto v___jp_136_;
}
}
else
{
v_lhs_137_ = v___x_140_;
v_rhs_138_ = v___x_141_;
goto v___jp_136_;
}
v___jp_136_:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(v_w_36_, v_n_133_, v_lhs_137_, v_rhs_138_);
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(lean_object* v_inst_148_, lean_object* v_w_149_, lean_object* v_expr_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___f_154_; lean_object* v_key_155_; lean_object* v___x_156_; lean_object* v_exprMap_157_; lean_object* v___f_158_; lean_object* v___x_159_; 
v___f_154_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__0));
lean_inc_ref(v_expr_150_);
lean_inc(v_w_149_);
v_key_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_155_, 0, v_w_149_);
lean_ctor_set(v_key_155_, 1, v_expr_150_);
v___x_156_ = lean_st_ref_get(v_a_152_);
v_exprMap_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc_ref(v_exprMap_157_);
lean_dec(v___x_156_);
v___f_158_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___closed__1);
lean_inc_ref(v_key_155_);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v___f_158_, v___f_154_, v_exprMap_157_, v_key_155_);
lean_dec_ref(v_exprMap_157_);
if (lean_obj_tag(v___x_159_) == 1)
{
lean_object* v_val_160_; 
lean_dec_ref_known(v_key_155_, 2);
lean_dec_ref(v_expr_150_);
lean_dec(v_w_149_);
lean_dec_ref(v_inst_148_);
v_val_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v___x_159_, 1);
return v_val_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_exprMap_163_; lean_object* v_logicalMap_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_173_; 
lean_dec(v___x_159_);
v___x_161_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg(v_inst_148_, v_w_149_, v_expr_150_, v_a_151_, v_a_152_);
v___x_162_ = lean_st_ref_take(v_a_152_);
v_exprMap_163_ = lean_ctor_get(v___x_162_, 0);
v_logicalMap_164_ = lean_ctor_get(v___x_162_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_173_ == 0)
{
v___x_166_ = v___x_162_;
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_logicalMap_164_);
lean_inc(v_exprMap_163_);
lean_dec(v___x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc_ref(v___x_161_);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_158_, v___f_154_, v_exprMap_163_, v_key_155_, v___x_161_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_logicalMap_164_);
v___x_170_ = v_reuseFailAlloc_172_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; 
v___x_171_ = lean_st_ref_put(v_a_152_, v___x_170_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg___boxed(lean_object* v_inst_174_, lean_object* v_w_175_, lean_object* v_expr_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_174_, v_w_175_, v_expr_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec(v_a_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg___boxed(lean_object* v_inst_181_, lean_object* v_w_182_, lean_object* v_expr_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg(v_inst_181_, v_w_182_, v_expr_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec(v_a_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go(lean_object* v_00_u03b1_188_, lean_object* v_inst_189_, lean_object* v_00_u03c3_190_, lean_object* v_w_191_, lean_object* v_expr_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___redArg(v_inst_189_, v_w_191_, v_expr_192_, v_a_193_, v_a_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go___boxed(lean_object* v_00_u03b1_197_, lean_object* v_inst_198_, lean_object* v_00_u03c3_199_, lean_object* v_w_200_, lean_object* v_expr_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM_go(v_00_u03b1_197_, v_inst_198_, v_00_u03c3_199_, v_w_200_, v_expr_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec(v_a_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_w_208_, lean_object* v_00_u03c3_209_, lean_object* v_expr_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_207_, v_w_208_, v_expr_210_, v_a_211_, v_a_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___boxed(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_w_217_, lean_object* v_00_u03c3_218_, lean_object* v_expr_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM(v_00_u03b1_215_, v_inst_216_, v_w_217_, v_00_u03c3_218_, v_expr_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec(v_a_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(lean_object* v_inst_224_, lean_object* v_pred_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
if (lean_obj_tag(v_pred_225_) == 0)
{
lean_object* v_w_229_; lean_object* v_lhs_230_; uint8_t v_op_231_; lean_object* v_rhs_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_251_; 
v_w_229_ = lean_ctor_get(v_pred_225_, 0);
v_lhs_230_ = lean_ctor_get(v_pred_225_, 1);
v_op_231_ = lean_ctor_get_uint8(v_pred_225_, sizeof(void*)*3);
v_rhs_232_ = lean_ctor_get(v_pred_225_, 2);
v_isSharedCheck_251_ = !lean_is_exclusive(v_pred_225_);
if (v_isSharedCheck_251_ == 0)
{
v___x_234_ = v_pred_225_;
v_isShared_235_ = v_isSharedCheck_251_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_rhs_232_);
lean_inc(v_lhs_230_);
lean_inc(v_w_229_);
lean_dec(v_pred_225_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_251_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_lhs_237_; lean_object* v_rhs_238_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_inc_n(v_w_229_, 2);
lean_inc_ref(v_inst_224_);
v___x_243_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_224_, v_w_229_, v_lhs_230_, v_a_226_, v_a_227_);
v___x_244_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_224_, v_w_229_, v_rhs_232_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_243_) == 1)
{
if (lean_obj_tag(v___x_244_) == 1)
{
lean_object* v_val_245_; lean_object* v_val_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
lean_del_object(v___x_234_);
lean_dec(v_w_229_);
v_val_245_ = lean_ctor_get(v___x_243_, 1);
lean_inc(v_val_245_);
lean_dec_ref_known(v___x_243_, 2);
v_val_246_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_val_246_);
lean_dec_ref_known(v___x_244_, 2);
v___x_247_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_231_, v_val_245_, v_val_246_);
lean_dec(v_val_246_);
lean_dec(v_val_245_);
v___x_248_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_247_);
return v___x_248_;
}
else
{
lean_object* v_val_249_; lean_object* v___x_250_; 
v_val_249_ = lean_ctor_get(v___x_243_, 1);
lean_inc(v_val_249_);
lean_dec_ref_known(v___x_243_, 2);
lean_inc(v_w_229_);
v___x_250_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_229_, v_val_249_);
v_lhs_237_ = v___x_250_;
v_rhs_238_ = v___x_244_;
goto v___jp_236_;
}
}
else
{
v_lhs_237_ = v___x_243_;
v_rhs_238_ = v___x_244_;
goto v___jp_236_;
}
v___jp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 2, v_rhs_238_);
lean_ctor_set(v___x_234_, 1, v_lhs_237_);
v___x_240_ = v___x_234_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_w_229_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_lhs_237_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_rhs_238_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, sizeof(void*)*3, v_op_231_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_Tactic_BVDecide_BVLogicalExpr_literal___override(v___x_240_);
return v___x_241_;
}
}
}
}
else
{
lean_object* v_w_252_; lean_object* v_expr_253_; lean_object* v_idx_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_266_; 
v_w_252_ = lean_ctor_get(v_pred_225_, 0);
v_expr_253_ = lean_ctor_get(v_pred_225_, 1);
v_idx_254_ = lean_ctor_get(v_pred_225_, 2);
v_isSharedCheck_266_ = !lean_is_exclusive(v_pred_225_);
if (v_isSharedCheck_266_ == 0)
{
v___x_256_ = v_pred_225_;
v_isShared_257_ = v_isSharedCheck_266_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_idx_254_);
lean_inc(v_expr_253_);
lean_inc(v_w_252_);
lean_dec(v_pred_225_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_266_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; 
lean_inc(v_w_252_);
v___x_258_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_224_, v_w_252_, v_expr_253_, v_a_226_, v_a_227_);
if (lean_obj_tag(v___x_258_) == 1)
{
lean_object* v_val_259_; uint8_t v___x_260_; lean_object* v___x_261_; 
lean_del_object(v___x_256_);
lean_dec(v_w_252_);
v_val_259_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_val_259_);
lean_dec_ref_known(v___x_258_, 2);
v___x_260_ = l_Nat_testBit(v_val_259_, v_idx_254_);
lean_dec(v_idx_254_);
lean_dec(v_val_259_);
v___x_261_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_263_; 
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_258_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_w_252_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_265_, 2, v_idx_254_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = l_Std_Tactic_BVDecide_BVLogicalExpr_literal___override(v___x_263_);
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg___boxed(lean_object* v_inst_267_, lean_object* v_pred_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_267_, v_pred_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec(v_a_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM(lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_00_u03c3_275_, lean_object* v_pred_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_274_, v_pred_276_, v_a_277_, v_a_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___boxed(lean_object* v_00_u03b1_281_, lean_object* v_inst_282_, lean_object* v_00_u03c3_283_, lean_object* v_pred_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM(v_00_u03b1_281_, v_inst_282_, v_00_u03c3_283_, v_pred_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec(v_a_285_);
return v_res_288_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0(void){
_start:
{
uint8_t v___x_289_; lean_object* v___x_290_; 
v___x_289_ = 1;
v___x_290_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1(void){
_start:
{
uint8_t v___x_291_; lean_object* v___x_292_; 
v___x_291_ = 0;
v___x_292_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(lean_object* v_x_293_){
_start:
{
switch(lean_obj_tag(v_x_293_))
{
case 1:
{
uint8_t v_a_294_; 
v_a_294_ = lean_ctor_get_uint8(v_x_293_, 8);
lean_dec_ref_known(v_x_293_, 0);
if (v_a_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1);
return v___x_296_;
}
}
case 2:
{
lean_object* v_a_297_; 
v_a_297_ = lean_ctor_get(v_x_293_, 0);
lean_inc_ref(v_a_297_);
lean_dec_ref_known(v_x_293_, 1);
return v_a_297_;
}
default: 
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_Tactic_BVDecide_BVLogicalExpr_not___override(v_x_293_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkGate(uint8_t v_g_299_, lean_object* v_x_300_, lean_object* v_y_301_){
_start:
{
if (lean_obj_tag(v_x_300_) == 1)
{
if (lean_obj_tag(v_y_301_) == 1)
{
uint8_t v_a_306_; uint8_t v_a_307_; uint8_t v___x_308_; lean_object* v___x_309_; 
v_a_306_ = lean_ctor_get_uint8(v_x_300_, 8);
lean_dec_ref_known(v_x_300_, 0);
v_a_307_ = lean_ctor_get_uint8(v_y_301_, 8);
lean_dec_ref_known(v_y_301_, 0);
v___x_308_ = l_Std_Tactic_BVDecide_Gate_eval(v_g_299_, v_a_306_, v_a_307_);
v___x_309_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v___x_308_);
return v___x_309_;
}
else
{
uint8_t v_a_310_; 
v_a_310_ = lean_ctor_get_uint8(v_x_300_, 8);
lean_dec_ref_known(v_x_300_, 0);
if (v_a_310_ == 0)
{
switch(v_g_299_)
{
case 0:
{
lean_dec_ref(v_y_301_);
goto v___jp_302_;
}
case 2:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(v_y_301_);
return v___x_311_;
}
default: 
{
return v_y_301_;
}
}
}
else
{
switch(v_g_299_)
{
case 1:
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(v_y_301_);
return v___x_312_;
}
case 3:
{
lean_dec_ref(v_y_301_);
goto v___jp_304_;
}
default: 
{
return v_y_301_;
}
}
}
}
}
else
{
switch(v_g_299_)
{
case 0:
{
if (lean_obj_tag(v_y_301_) == 1)
{
uint8_t v_a_313_; 
v_a_313_ = lean_ctor_get_uint8(v_y_301_, 8);
lean_dec_ref_known(v_y_301_, 0);
if (v_a_313_ == 0)
{
lean_dec_ref(v_x_300_);
goto v___jp_302_;
}
else
{
return v_x_300_;
}
}
else
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(v_g_299_, v_x_300_, v_y_301_);
return v___x_314_;
}
}
case 1:
{
if (lean_obj_tag(v_y_301_) == 1)
{
uint8_t v_a_315_; 
v_a_315_ = lean_ctor_get_uint8(v_y_301_, 8);
lean_dec_ref_known(v_y_301_, 0);
if (v_a_315_ == 0)
{
return v_x_300_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(v_x_300_);
return v___x_316_;
}
}
else
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(v_g_299_, v_x_300_, v_y_301_);
return v___x_317_;
}
}
case 2:
{
if (lean_obj_tag(v_y_301_) == 1)
{
uint8_t v_a_318_; 
v_a_318_ = lean_ctor_get_uint8(v_y_301_, 8);
lean_dec_ref_known(v_y_301_, 0);
if (v_a_318_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(v_x_300_);
return v___x_319_;
}
else
{
return v_x_300_;
}
}
else
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(v_g_299_, v_x_300_, v_y_301_);
return v___x_320_;
}
}
default: 
{
if (lean_obj_tag(v_y_301_) == 1)
{
uint8_t v_a_321_; 
v_a_321_ = lean_ctor_get_uint8(v_y_301_, 8);
lean_dec_ref_known(v_y_301_, 0);
if (v_a_321_ == 0)
{
return v_x_300_;
}
else
{
lean_dec_ref(v_x_300_);
goto v___jp_304_;
}
}
else
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(v_g_299_, v_x_300_, v_y_301_);
return v___x_322_;
}
}
}
}
v___jp_302_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__1);
return v___x_303_;
}
v___jp_304_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot___closed__0);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkGate___boxed(lean_object* v_g_323_, lean_object* v_x_324_, lean_object* v_y_325_){
_start:
{
uint8_t v_g_boxed_326_; lean_object* v_res_327_; 
v_g_boxed_326_ = lean_unbox(v_g_323_);
v_res_327_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkGate(v_g_boxed_326_, v_x_324_, v_y_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg(lean_object* v_inst_332_, lean_object* v_expr_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
switch(lean_obj_tag(v_expr_333_))
{
case 0:
{
lean_object* v_a_337_; 
v_a_337_ = lean_ctor_get(v_expr_333_, 0);
lean_inc_ref(v_a_337_);
lean_dec_ref_known(v_expr_333_, 1);
if (lean_obj_tag(v_a_337_) == 1)
{
lean_object* v_w_338_; lean_object* v_expr_339_; lean_object* v_idx_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_w_338_ = lean_ctor_get(v_a_337_, 0);
v_expr_339_ = lean_ctor_get(v_a_337_, 1);
v_idx_340_ = lean_ctor_get(v_a_337_, 2);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_dec_eq(v_w_338_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_332_, v_a_337_, v_a_334_, v_a_335_);
return v___x_343_;
}
else
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_368_; 
lean_inc(v_idx_340_);
lean_inc_ref(v_expr_339_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_a_337_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_369_ = lean_ctor_get(v_a_337_, 2);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_a_337_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_a_337_, 0);
lean_dec(v_unused_371_);
v___x_345_ = v_a_337_;
v_isShared_346_ = v_isSharedCheck_368_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_a_337_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_368_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
if (lean_obj_tag(v_expr_339_) == 0)
{
lean_object* v_idx_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_idx_347_ = lean_ctor_get(v_expr_339_, 1);
lean_inc(v_idx_347_);
lean_dec_ref_known(v_expr_339_, 2);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v_idx_340_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v___x_341_, v_idx_347_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_350_);
lean_ctor_set(v___x_345_, 0, v___x_341_);
v___x_352_ = v___x_345_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_idx_340_);
v___x_352_ = v_reuseFailAlloc_354_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_332_, v___x_352_, v_a_334_, v_a_335_);
return v___x_353_;
}
}
else
{
lean_object* v_boolAtom_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec(v_idx_340_);
v_boolAtom_355_ = lean_ctor_get(v_inst_332_, 1);
lean_inc(v_idx_347_);
v___x_356_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v___x_341_, v_idx_347_);
lean_inc_ref(v_boolAtom_355_);
lean_inc(v_a_334_);
v___x_357_ = lean_apply_2(v_boolAtom_355_, v_a_334_, v_idx_347_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v___x_359_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 2, v___x_348_);
lean_ctor_set(v___x_345_, 1, v___x_356_);
lean_ctor_set(v___x_345_, 0, v___x_341_);
v___x_359_ = v___x_345_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v___x_348_);
v___x_359_ = v_reuseFailAlloc_361_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_332_, v___x_359_, v_a_334_, v_a_335_);
return v___x_360_;
}
}
else
{
lean_object* v_val_362_; lean_object* v___x_363_; 
lean_dec_ref(v___x_356_);
lean_del_object(v___x_345_);
v_val_362_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_val_362_);
lean_dec_ref_known(v___x_357_, 1);
v___x_363_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_val_362_, v_a_334_, v_a_335_);
return v___x_363_;
}
}
}
else
{
lean_object* v___x_365_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_341_);
v___x_365_ = v___x_345_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_expr_339_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_idx_340_);
v___x_365_ = v_reuseFailAlloc_367_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_332_, v___x_365_, v_a_334_, v_a_335_);
return v___x_366_;
}
}
}
}
}
else
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVPred_substM___redArg(v_inst_332_, v_a_337_, v_a_334_, v_a_335_);
return v___x_372_;
}
}
case 1:
{
lean_dec_ref(v_inst_332_);
return v_expr_333_;
}
case 2:
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_373_ = lean_ctor_get(v_expr_333_, 0);
lean_inc_ref(v_a_373_);
lean_dec_ref_known(v_expr_333_, 1);
v___x_374_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_373_, v_a_334_, v_a_335_);
v___x_375_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkNot(v___x_374_);
return v___x_375_;
}
case 3:
{
uint8_t v_a_376_; lean_object* v_a_377_; lean_object* v_a_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_376_ = lean_ctor_get_uint8(v_expr_333_, sizeof(void*)*2 + 8);
v_a_377_ = lean_ctor_get(v_expr_333_, 0);
lean_inc_ref(v_a_377_);
v_a_378_ = lean_ctor_get(v_expr_333_, 1);
lean_inc_ref(v_a_378_);
lean_dec_ref_known(v_expr_333_, 2);
lean_inc_ref(v_inst_332_);
v___x_379_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_377_, v_a_334_, v_a_335_);
v___x_380_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_378_, v_a_334_, v_a_335_);
v___x_381_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_mkGate(v_a_376_, v___x_379_, v___x_380_);
return v___x_381_;
}
default: 
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_382_ = lean_ctor_get(v_expr_333_, 0);
lean_inc_ref(v_a_382_);
v_a_383_ = lean_ctor_get(v_expr_333_, 1);
lean_inc_ref(v_a_383_);
v_a_384_ = lean_ctor_get(v_expr_333_, 2);
lean_inc_ref(v_a_384_);
lean_dec_ref_known(v_expr_333_, 3);
lean_inc_ref(v_inst_332_);
v___x_385_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_382_, v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_385_) == 1)
{
uint8_t v_a_386_; 
v_a_386_ = lean_ctor_get_uint8(v___x_385_, 8);
lean_dec_ref_known(v___x_385_, 0);
if (v_a_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec_ref(v_a_383_);
v___x_387_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_384_, v_a_334_, v_a_335_);
return v___x_387_;
}
else
{
lean_object* v___x_388_; 
lean_dec_ref(v_a_384_);
v___x_388_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_383_, v_a_334_, v_a_335_);
return v___x_388_;
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc_ref(v_inst_332_);
v___x_389_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_383_, v_a_334_, v_a_335_);
v___x_390_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_332_, v_a_384_, v_a_334_, v_a_335_);
v___x_391_ = l_Std_Tactic_BVDecide_BVLogicalExpr_ite___override(v___x_385_, v___x_389_, v___x_390_);
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(lean_object* v_inst_392_, lean_object* v_expr_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v_logicalMap_399_; lean_object* v___f_400_; lean_object* v___x_401_; 
v___f_397_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__0));
v___x_398_ = lean_st_ref_get(v_a_395_);
v_logicalMap_399_ = lean_ctor_get(v___x_398_, 1);
lean_inc_ref(v_logicalMap_399_);
lean_dec(v___x_398_);
v___f_400_ = ((lean_object*)(l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___closed__2));
lean_inc_ref(v_expr_393_);
v___x_401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_400_, v___f_397_, v_logicalMap_399_, v_expr_393_);
lean_dec_ref(v_logicalMap_399_);
if (lean_obj_tag(v___x_401_) == 1)
{
lean_object* v_val_402_; 
lean_dec_ref(v_expr_393_);
lean_dec_ref(v_inst_392_);
v_val_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_401_, 1);
return v_val_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_exprMap_405_; lean_object* v_logicalMap_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_415_; 
lean_dec(v___x_401_);
lean_inc_ref(v_expr_393_);
v___x_403_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg(v_inst_392_, v_expr_393_, v_a_394_, v_a_395_);
v___x_404_ = lean_st_ref_take(v_a_395_);
v_exprMap_405_ = lean_ctor_get(v___x_404_, 0);
v_logicalMap_406_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_415_ == 0)
{
v___x_408_ = v___x_404_;
v_isShared_409_ = v_isSharedCheck_415_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_logicalMap_406_);
lean_inc(v_exprMap_405_);
lean_dec(v___x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_415_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
lean_inc_ref(v___x_403_);
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_400_, v___f_397_, v_logicalMap_406_, v_expr_393_, v___x_403_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_410_);
v___x_412_ = v___x_408_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_exprMap_405_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_414_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; 
v___x_413_ = lean_st_ref_put(v_a_395_, v___x_412_);
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg___boxed(lean_object* v_inst_416_, lean_object* v_expr_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_416_, v_expr_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec(v_a_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg___boxed(lean_object* v_inst_422_, lean_object* v_expr_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg(v_inst_422_, v_expr_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec(v_a_424_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go(lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_00_u03c3_430_, lean_object* v_expr_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___redArg(v_inst_429_, v_expr_431_, v_a_432_, v_a_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go___boxed(lean_object* v_00_u03b1_436_, lean_object* v_inst_437_, lean_object* v_00_u03c3_438_, lean_object* v_expr_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM_go(v_00_u03b1_436_, v_inst_437_, v_00_u03c3_438_, v_expr_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec(v_a_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM(lean_object* v_00_u03b1_444_, lean_object* v_inst_445_, lean_object* v_00_u03c3_446_, lean_object* v_expr_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_445_, v_expr_447_, v_a_448_, v_a_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___boxed(lean_object* v_00_u03b1_452_, lean_object* v_inst_453_, lean_object* v_00_u03c3_454_, lean_object* v_expr_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM(v_00_u03b1_452_, v_inst_453_, v_00_u03c3_454_, v_expr_455_, v_a_456_, v_a_457_);
lean_dec(v_a_457_);
lean_dec(v_a_456_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute___redArg___lam__0(lean_object* v_inst_460_, lean_object* v_w_461_, lean_object* v_expr_462_, lean_object* v_subst_463_, lean_object* v_00_u03c3_464_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2);
v___x_467_ = lean_st_mk_ref(v___x_466_);
v___x_468_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVExpr_substM___redArg(v_inst_460_, v_w_461_, v_expr_462_, v_subst_463_, v___x_467_);
v___x_469_ = lean_st_ref_get(v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_469_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute___redArg___lam__0___boxed(lean_object* v_inst_470_, lean_object* v_w_471_, lean_object* v_expr_472_, lean_object* v_subst_473_, lean_object* v_00_u03c3_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Tactic_BVDecide_BVExpr_substitute___redArg___lam__0(v_inst_470_, v_w_471_, v_expr_472_, v_subst_473_, v_00_u03c3_474_);
lean_dec(v_subst_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute___redArg(lean_object* v_w_477_, lean_object* v_inst_478_, lean_object* v_subst_479_, lean_object* v_expr_480_){
_start:
{
lean_object* v___f_481_; lean_object* v___x_482_; 
v___f_481_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_substitute___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_481_, 0, v_inst_478_);
lean_closure_set(v___f_481_, 1, v_w_477_);
lean_closure_set(v___f_481_, 2, v_expr_480_);
lean_closure_set(v___f_481_, 3, v_subst_479_);
v___x_482_ = l_runST___redArg(v___f_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_substitute(lean_object* v_00_u03b1_483_, lean_object* v_w_484_, lean_object* v_inst_485_, lean_object* v_subst_486_, lean_object* v_expr_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_Tactic_BVDecide_BVExpr_substitute___redArg(v_w_484_, v_inst_485_, v_subst_486_, v_expr_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg___lam__0(lean_object* v_inst_489_, lean_object* v_expr_490_, lean_object* v_subst_491_, lean_object* v_00_u03c3_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_494_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2);
v___x_495_ = lean_st_mk_ref(v___x_494_);
v___x_496_ = l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___redArg(v_inst_489_, v_expr_490_, v_subst_491_, v___x_495_);
v___x_497_ = lean_st_ref_get(v___x_495_);
lean_dec(v___x_495_);
lean_dec(v___x_497_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg___lam__0___boxed(lean_object* v_inst_498_, lean_object* v_expr_499_, lean_object* v_subst_500_, lean_object* v_00_u03c3_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg___lam__0(v_inst_498_, v_expr_499_, v_subst_500_, v_00_u03c3_501_);
lean_dec(v_subst_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg(lean_object* v_inst_504_, lean_object* v_subst_505_, lean_object* v_expr_506_){
_start:
{
lean_object* v___f_507_; lean_object* v___x_508_; 
v___f_507_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_507_, 0, v_inst_504_);
lean_closure_set(v___f_507_, 1, v_expr_506_);
lean_closure_set(v___f_507_, 2, v_subst_505_);
v___x_508_ = l_runST___redArg(v___f_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substitute(lean_object* v_00_u03b1_509_, lean_object* v_inst_510_, lean_object* v_subst_511_, lean_object* v_expr_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_Tactic_BVDecide_BVLogicalExpr_substitute___redArg(v_inst_510_, v_subst_511_, v_expr_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_instMonadST___redArg();
return v___x_514_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__0, &l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__0_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__0);
v___x_516_ = l_StateRefT_x27_instMonad___redArg(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__1, &l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__1_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__1);
v___x_518_ = l_ReaderT_instMonad___redArg(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0(lean_object* v_inst_519_, lean_object* v_exprs_520_, lean_object* v_subst_521_, lean_object* v_00_u03c3_522_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_82__overap_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_524_ = lean_obj_once(&l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2, &l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2_once, _init_l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_SubstM_run___redArg___lam__0___closed__2);
v___x_525_ = lean_st_mk_ref(v___x_524_);
v___x_526_ = lean_obj_once(&l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__2, &l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__2_once, _init_l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___closed__2);
v___x_527_ = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_Substitute_0__Std_Tactic_BVDecide_Substitute_BVLogicalExpr_substM___boxed), 7, 3);
lean_closure_set(v___x_527_, 0, lean_box(0));
lean_closure_set(v___x_527_, 1, v_inst_519_);
lean_closure_set(v___x_527_, 2, lean_box(0));
v_sz_528_ = lean_array_size(v_exprs_520_);
v___x_529_ = ((size_t)0ULL);
v___x_82__overap_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_526_, v___x_527_, v_sz_528_, v___x_529_, v_exprs_520_);
lean_inc(v___x_525_);
v___x_531_ = lean_apply_3(v___x_82__overap_530_, v_subst_521_, v___x_525_, lean_box(0));
v___x_532_ = lean_st_ref_get(v___x_525_);
lean_dec(v___x_525_);
lean_dec(v___x_532_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___boxed(lean_object* v_inst_533_, lean_object* v_exprs_534_, lean_object* v_subst_535_, lean_object* v_00_u03c3_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0(v_inst_533_, v_exprs_534_, v_subst_535_, v_00_u03c3_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg(lean_object* v_inst_539_, lean_object* v_subst_540_, lean_object* v_exprs_541_){
_start:
{
lean_object* v___f_542_; lean_object* v___x_543_; 
v___f_542_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_542_, 0, v_inst_539_);
lean_closure_set(v___f_542_, 1, v_exprs_541_);
lean_closure_set(v___f_542_, 2, v_subst_540_);
v___x_543_ = l_runST___redArg(v___f_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll(lean_object* v_00_u03b1_544_, lean_object* v_inst_545_, lean_object* v_subst_546_, lean_object* v_exprs_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_Tactic_BVDecide_BVLogicalExpr_substituteAll___redArg(v_inst_545_, v_subst_546_, v_exprs_547_);
return v___x_548_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_ST(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_Substitute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_Substitute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Init_System_ST(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_Substitute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_Substitute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_Substitute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_Substitute(builtin);
}
#ifdef __cplusplus
}
#endif
