// Lean compiler output
// Module: Lean.Compiler.IR.EmitUtil
// Imports: public import Lean.Compiler.InitAttr public import Lean.Compiler.IR.CompilerM
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
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_IR_instHashableVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_instHashableJoinPointId_hash___boxed(lean_object*);
uint64_t l_Lean_IR_instHashableJoinPointId_hash(lean_object*);
uint8_t l_Lean_IR_instBEqJoinPointId_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_IR_instBEqJoinPointId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_instBEqVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_instHashableVarId_hash___boxed(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT uint8_t l_Lean_IR_isTailCallTo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_isTailCallTo___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_usesModuleFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_usesModuleFrom___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0 = (const lean_object*)&l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_collectUsedDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_collectUsedDecls___closed__0 = (const lean_object*)&l_Lean_IR_collectUsedDecls___closed__0_value;
static lean_once_cell_t l_Lean_IR_collectUsedDecls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_collectUsedDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_CollectMaps_collectVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectMaps_collectVar___closed__0 = (const lean_object*)&l_Lean_IR_CollectMaps_collectVar___closed__0_value;
static const lean_closure_object l_Lean_IR_CollectMaps_collectVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instHashableVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectMaps_collectVar___closed__1 = (const lean_object*)&l_Lean_IR_CollectMaps_collectVar___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_CollectMaps_collectJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqJoinPointId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectMaps_collectJP___closed__0 = (const lean_object*)&l_Lean_IR_CollectMaps_collectJP___closed__0_value;
static const lean_closure_object l_Lean_IR_CollectMaps_collectJP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instHashableJoinPointId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectMaps_collectJP___closed__1 = (const lean_object*)&l_Lean_IR_CollectMaps_collectJP___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__0;
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__1;
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_isTailCallTo(lean_object* v_g_1_, lean_object* v_b_2_){
_start:
{
if (lean_obj_tag(v_b_2_) == 0)
{
lean_object* v_e_3_; 
v_e_3_ = lean_ctor_get(v_b_2_, 2);
if (lean_obj_tag(v_e_3_) == 6)
{
lean_object* v_b_4_; 
v_b_4_ = lean_ctor_get(v_b_2_, 3);
if (lean_obj_tag(v_b_4_) == 10)
{
lean_object* v_x_5_; 
v_x_5_ = lean_ctor_get(v_b_4_, 0);
if (lean_obj_tag(v_x_5_) == 0)
{
lean_object* v_x_6_; lean_object* v_c_7_; lean_object* v_id_8_; uint8_t v___x_9_; 
v_x_6_ = lean_ctor_get(v_b_2_, 0);
v_c_7_ = lean_ctor_get(v_e_3_, 0);
v_id_8_ = lean_ctor_get(v_x_5_, 0);
v___x_9_ = l_Lean_IR_instBEqVarId_beq(v_x_6_, v_id_8_);
if (v___x_9_ == 0)
{
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = lean_name_eq(v_c_7_, v_g_1_);
return v___x_10_;
}
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
else
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
}
else
{
uint8_t v___x_14_; 
v___x_14_ = 0;
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_isTailCallTo___boxed(lean_object* v_g_15_, lean_object* v_b_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_IR_isTailCallTo(v_g_15_, v_b_16_);
lean_dec(v_b_16_);
lean_dec(v_g_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(lean_object* v_modulePrefix_19_, lean_object* v_as_20_, size_t v_i_21_, size_t v_stop_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = lean_usize_dec_eq(v_i_21_, v_stop_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v_toImport_25_; uint8_t v_irPhases_26_; uint8_t v___x_27_; uint8_t v___y_29_; uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_24_ = lean_array_uget_borrowed(v_as_20_, v_i_21_);
v_toImport_25_ = lean_ctor_get(v___x_24_, 0);
v_irPhases_26_ = lean_ctor_get_uint8(v___x_24_, sizeof(void*)*1);
v___x_27_ = 1;
v___x_33_ = 1;
v___x_34_ = l_Lean_instBEqIRPhases_beq(v_irPhases_26_, v___x_33_);
if (v___x_34_ == 0)
{
lean_object* v_module_35_; uint8_t v___x_36_; 
v_module_35_ = lean_ctor_get(v_toImport_25_, 0);
v___x_36_ = l_Lean_Name_isPrefixOf(v_modulePrefix_19_, v_module_35_);
v___y_29_ = v___x_36_;
goto v___jp_28_;
}
else
{
v___y_29_ = v___x_23_;
goto v___jp_28_;
}
v___jp_28_:
{
if (v___y_29_ == 0)
{
size_t v___x_30_; size_t v___x_31_; 
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_add(v_i_21_, v___x_30_);
v_i_21_ = v___x_31_;
goto _start;
}
else
{
return v___x_27_;
}
}
}
else
{
uint8_t v___x_37_; 
v___x_37_ = 0;
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_38_, lean_object* v_as_39_, lean_object* v_i_40_, lean_object* v_stop_41_){
_start:
{
size_t v_i_boxed_42_; size_t v_stop_boxed_43_; uint8_t v_res_44_; lean_object* v_r_45_; 
v_i_boxed_42_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_stop_boxed_43_ = lean_unbox_usize(v_stop_41_);
lean_dec(v_stop_41_);
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_38_, v_as_39_, v_i_boxed_42_, v_stop_boxed_43_);
lean_dec_ref(v_as_39_);
lean_dec(v_modulePrefix_38_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_usesModuleFrom(lean_object* v_env_46_, lean_object* v_modulePrefix_47_){
_start:
{
lean_object* v___x_48_; lean_object* v_modules_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_48_ = l_Lean_Environment_header(v_env_46_);
v_modules_49_ = lean_ctor_get(v___x_48_, 3);
lean_inc_ref(v_modules_49_);
lean_dec_ref(v___x_48_);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_array_get_size(v_modules_49_);
v___x_52_ = lean_nat_dec_lt(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec_ref(v_modules_49_);
return v___x_52_;
}
else
{
if (v___x_52_ == 0)
{
lean_dec_ref(v_modules_49_);
return v___x_52_;
}
else
{
size_t v___x_53_; size_t v___x_54_; uint8_t v___x_55_; 
v___x_53_ = ((size_t)0ULL);
v___x_54_ = lean_usize_of_nat(v___x_51_);
v___x_55_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_47_, v_modules_49_, v___x_53_, v___x_54_);
lean_dec_ref(v_modules_49_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_usesModuleFrom___boxed(lean_object* v_env_56_, lean_object* v_modulePrefix_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_IR_usesModuleFrom(v_env_56_, v_modulePrefix_57_);
lean_dec(v_modulePrefix_57_);
lean_dec_ref(v_env_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___redArg(lean_object* v_f_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_set_63_; lean_object* v_order_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_87_; 
v_set_63_ = lean_ctor_get(v_a_62_, 0);
v_order_64_ = lean_ctor_get(v_a_62_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_a_62_);
if (v_isSharedCheck_87_ == 0)
{
v___x_66_ = v_a_62_;
v_isShared_67_ = v_isSharedCheck_87_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_order_64_);
lean_inc(v_set_63_);
lean_dec(v_a_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_87_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v_fst_70_; lean_object* v_snd_71_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_68_ = lean_box(0);
v___x_82_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_63_);
lean_inc(v_f_61_);
v___x_83_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_82_, v_f_61_, v_set_63_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_inc(v_f_61_);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_82_, v_f_61_, v___x_68_, v_set_63_);
v___x_85_ = lean_box(v___x_83_);
v_fst_70_ = v___x_85_;
v_snd_71_ = v___x_84_;
goto v___jp_69_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(v___x_83_);
v_fst_70_ = v___x_86_;
v_snd_71_ = v_set_63_;
goto v___jp_69_;
}
v___jp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = lean_unbox(v_fst_70_);
lean_dec(v_fst_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_array_push(v_order_64_, v_f_61_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_73_);
lean_ctor_set(v___x_66_, 0, v_snd_71_);
v___x_75_ = v___x_66_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_snd_71_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_73_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_68_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
return v___x_76_;
}
}
else
{
lean_object* v___x_79_; 
lean_dec(v_f_61_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v_snd_71_);
v___x_79_ = v___x_66_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_snd_71_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_order_64_);
v___x_79_ = v_reuseFailAlloc_81_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_68_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* v_f_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_set_91_; lean_object* v_order_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_115_; 
v_set_91_ = lean_ctor_get(v_a_90_, 0);
v_order_92_ = lean_ctor_get(v_a_90_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_a_90_);
if (v_isSharedCheck_115_ == 0)
{
v___x_94_ = v_a_90_;
v_isShared_95_ = v_isSharedCheck_115_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_order_92_);
lean_inc(v_set_91_);
lean_dec(v_a_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_115_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_96_ = lean_box(0);
v___x_110_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_91_);
lean_inc(v_f_88_);
v___x_111_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_110_, v_f_88_, v_set_91_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_inc(v_f_88_);
v___x_112_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_110_, v_f_88_, v___x_96_, v_set_91_);
v___x_113_ = lean_box(v___x_111_);
v_fst_98_ = v___x_113_;
v_snd_99_ = v___x_112_;
goto v___jp_97_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(v___x_111_);
v_fst_98_ = v___x_114_;
v_snd_99_ = v_set_91_;
goto v___jp_97_;
}
v___jp_97_:
{
uint8_t v___x_100_; 
v___x_100_ = lean_unbox(v_fst_98_);
lean_dec(v_fst_98_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_array_push(v_order_92_, v_f_88_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v___x_101_);
lean_ctor_set(v___x_94_, 0, v_snd_99_);
v___x_103_ = v___x_94_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_snd_99_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_96_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
return v___x_104_;
}
}
else
{
lean_object* v___x_107_; 
lean_dec(v_f_88_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v_snd_99_);
v___x_107_ = v___x_94_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_snd_99_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_order_92_);
v___x_107_ = v_reuseFailAlloc_109_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_96_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
return v___x_108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* v_f_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_IR_CollectUsedDecls_collect(v_f_116_, v_a_117_, v_a_118_);
lean_dec_ref(v_a_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object* v_k_120_, lean_object* v_v_121_, lean_object* v_t_122_){
_start:
{
if (lean_obj_tag(v_t_122_) == 0)
{
lean_object* v_size_123_; lean_object* v_k_124_; lean_object* v_v_125_; lean_object* v_l_126_; lean_object* v_r_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_407_; 
v_size_123_ = lean_ctor_get(v_t_122_, 0);
v_k_124_ = lean_ctor_get(v_t_122_, 1);
v_v_125_ = lean_ctor_get(v_t_122_, 2);
v_l_126_ = lean_ctor_get(v_t_122_, 3);
v_r_127_ = lean_ctor_get(v_t_122_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v_t_122_);
if (v_isSharedCheck_407_ == 0)
{
v___x_129_ = v_t_122_;
v_isShared_130_ = v_isSharedCheck_407_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_r_127_);
lean_inc(v_l_126_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
lean_inc(v_size_123_);
lean_dec(v_t_122_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_407_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint8_t v___x_131_; 
v___x_131_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_120_, v_k_124_);
switch(v___x_131_)
{
case 0:
{
lean_object* v_impl_132_; lean_object* v___x_133_; 
lean_dec(v_size_123_);
v_impl_132_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_120_, v_v_121_, v_l_126_);
v___x_133_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_127_) == 0)
{
lean_object* v_size_134_; lean_object* v_size_135_; lean_object* v_k_136_; lean_object* v_v_137_; lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_size_134_ = lean_ctor_get(v_r_127_, 0);
v_size_135_ = lean_ctor_get(v_impl_132_, 0);
lean_inc(v_size_135_);
v_k_136_ = lean_ctor_get(v_impl_132_, 1);
lean_inc(v_k_136_);
v_v_137_ = lean_ctor_get(v_impl_132_, 2);
lean_inc(v_v_137_);
v_l_138_ = lean_ctor_get(v_impl_132_, 3);
lean_inc(v_l_138_);
v_r_139_ = lean_ctor_get(v_impl_132_, 4);
lean_inc(v_r_139_);
v___x_140_ = lean_unsigned_to_nat(3u);
v___x_141_ = lean_nat_mul(v___x_140_, v_size_134_);
v___x_142_ = lean_nat_dec_lt(v___x_141_, v_size_135_);
lean_dec(v___x_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_r_139_);
lean_dec(v_l_138_);
lean_dec(v_v_137_);
lean_dec(v_k_136_);
v___x_143_ = lean_nat_add(v___x_133_, v_size_135_);
lean_dec(v_size_135_);
v___x_144_ = lean_nat_add(v___x_143_, v_size_134_);
lean_dec(v___x_143_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 3, v_impl_132_);
lean_ctor_set(v___x_129_, 0, v___x_144_);
v___x_146_ = v___x_129_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_impl_132_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_r_127_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
else
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_213_; 
v_isSharedCheck_213_ = !lean_is_exclusive(v_impl_132_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_214_ = lean_ctor_get(v_impl_132_, 4);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_impl_132_, 3);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_impl_132_, 2);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_impl_132_, 1);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_impl_132_, 0);
lean_dec(v_unused_218_);
v___x_149_ = v_impl_132_;
v_isShared_150_ = v_isSharedCheck_213_;
goto v_resetjp_148_;
}
else
{
lean_dec(v_impl_132_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_213_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_size_151_; lean_object* v_size_152_; lean_object* v_k_153_; lean_object* v_v_154_; lean_object* v_l_155_; lean_object* v_r_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_size_151_ = lean_ctor_get(v_l_138_, 0);
v_size_152_ = lean_ctor_get(v_r_139_, 0);
v_k_153_ = lean_ctor_get(v_r_139_, 1);
v_v_154_ = lean_ctor_get(v_r_139_, 2);
v_l_155_ = lean_ctor_get(v_r_139_, 3);
v_r_156_ = lean_ctor_get(v_r_139_, 4);
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_nat_mul(v___x_157_, v_size_151_);
v___x_159_ = lean_nat_dec_lt(v_size_152_, v___x_158_);
lean_dec(v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_188_; 
lean_inc(v_r_156_);
lean_inc(v_l_155_);
lean_inc(v_v_154_);
lean_inc(v_k_153_);
v_isSharedCheck_188_ = !lean_is_exclusive(v_r_139_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; 
v_unused_189_ = lean_ctor_get(v_r_139_, 4);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_r_139_, 3);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_r_139_, 2);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_r_139_, 1);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_r_139_, 0);
lean_dec(v_unused_193_);
v___x_161_ = v_r_139_;
v_isShared_162_ = v_isSharedCheck_188_;
goto v_resetjp_160_;
}
else
{
lean_dec(v_r_139_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_188_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___x_176_; lean_object* v___y_178_; 
v___x_163_ = lean_nat_add(v___x_133_, v_size_135_);
lean_dec(v_size_135_);
v___x_164_ = lean_nat_add(v___x_163_, v_size_134_);
lean_dec(v___x_163_);
v___x_176_ = lean_nat_add(v___x_133_, v_size_151_);
if (lean_obj_tag(v_l_155_) == 0)
{
lean_object* v_size_186_; 
v_size_186_ = lean_ctor_get(v_l_155_, 0);
lean_inc(v_size_186_);
v___y_178_ = v_size_186_;
goto v___jp_177_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___y_178_ = v___x_187_;
goto v___jp_177_;
}
v___jp_165_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_nat_add(v___y_166_, v___y_168_);
lean_dec(v___y_168_);
lean_dec(v___y_166_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 4, v_r_127_);
lean_ctor_set(v___x_161_, 3, v_r_156_);
lean_ctor_set(v___x_161_, 2, v_v_125_);
lean_ctor_set(v___x_161_, 1, v_k_124_);
lean_ctor_set(v___x_161_, 0, v___x_169_);
v___x_171_ = v___x_161_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_127_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_173_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v___x_171_);
lean_ctor_set(v___x_149_, 3, v___y_167_);
lean_ctor_set(v___x_149_, 2, v_v_154_);
lean_ctor_set(v___x_149_, 1, v_k_153_);
lean_ctor_set(v___x_149_, 0, v___x_164_);
v___x_173_ = v___x_149_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_k_153_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_v_154_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___y_167_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_nat_add(v___x_176_, v___y_178_);
lean_dec(v___y_178_);
lean_dec(v___x_176_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_155_);
lean_ctor_set(v___x_129_, 3, v_l_138_);
lean_ctor_set(v___x_129_, 2, v_v_137_);
lean_ctor_set(v___x_129_, 1, v_k_136_);
lean_ctor_set(v___x_129_, 0, v___x_179_);
v___x_181_ = v___x_129_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_l_138_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v_l_155_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; 
v___x_182_ = lean_nat_add(v___x_133_, v_size_134_);
if (lean_obj_tag(v_r_156_) == 0)
{
lean_object* v_size_183_; 
v_size_183_ = lean_ctor_get(v_r_156_, 0);
lean_inc(v_size_183_);
v___y_166_ = v___x_182_;
v___y_167_ = v___x_181_;
v___y_168_ = v_size_183_;
goto v___jp_165_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___y_166_ = v___x_182_;
v___y_167_ = v___x_181_;
v___y_168_ = v___x_184_;
goto v___jp_165_;
}
}
}
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
lean_del_object(v___x_129_);
v___x_194_ = lean_nat_add(v___x_133_, v_size_135_);
lean_dec(v_size_135_);
v___x_195_ = lean_nat_add(v___x_194_, v_size_134_);
lean_dec(v___x_194_);
v___x_196_ = lean_nat_add(v___x_133_, v_size_134_);
v___x_197_ = lean_nat_add(v___x_196_, v_size_152_);
lean_dec(v___x_196_);
lean_inc_ref(v_r_127_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v_r_127_);
lean_ctor_set(v___x_149_, 3, v_r_139_);
lean_ctor_set(v___x_149_, 2, v_v_125_);
lean_ctor_set(v___x_149_, 1, v_k_124_);
lean_ctor_set(v___x_149_, 0, v___x_197_);
v___x_199_ = v___x_149_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_r_139_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_r_127_);
v___x_199_ = v_reuseFailAlloc_212_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_isSharedCheck_206_ = !lean_is_exclusive(v_r_127_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; 
v_unused_207_ = lean_ctor_get(v_r_127_, 4);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_r_127_, 3);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_r_127_, 2);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_r_127_, 1);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_r_127_, 0);
lean_dec(v_unused_211_);
v___x_201_ = v_r_127_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_dec(v_r_127_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 4, v___x_199_);
lean_ctor_set(v___x_201_, 3, v_l_138_);
lean_ctor_set(v___x_201_, 2, v_v_137_);
lean_ctor_set(v___x_201_, 1, v_k_136_);
lean_ctor_set(v___x_201_, 0, v___x_195_);
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_136_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_137_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_l_138_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v___x_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_219_; 
v_l_219_ = lean_ctor_get(v_impl_132_, 3);
lean_inc(v_l_219_);
if (lean_obj_tag(v_l_219_) == 0)
{
lean_object* v_r_220_; lean_object* v_k_221_; lean_object* v_v_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_233_; 
v_r_220_ = lean_ctor_get(v_impl_132_, 4);
v_k_221_ = lean_ctor_get(v_impl_132_, 1);
v_v_222_ = lean_ctor_get(v_impl_132_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_impl_132_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; lean_object* v_unused_235_; 
v_unused_234_ = lean_ctor_get(v_impl_132_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_impl_132_, 0);
lean_dec(v_unused_235_);
v___x_224_ = v_impl_132_;
v_isShared_225_ = v_isSharedCheck_233_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_r_220_);
lean_inc(v_v_222_);
lean_inc(v_k_221_);
lean_dec(v_impl_132_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_233_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_220_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 3, v_r_220_);
lean_ctor_set(v___x_224_, 2, v_v_125_);
lean_ctor_set(v___x_224_, 1, v_k_124_);
lean_ctor_set(v___x_224_, 0, v___x_133_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_r_220_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_r_220_);
v___x_228_ = v_reuseFailAlloc_232_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_230_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_228_);
lean_ctor_set(v___x_129_, 3, v_l_219_);
lean_ctor_set(v___x_129_, 2, v_v_222_);
lean_ctor_set(v___x_129_, 1, v_k_221_);
lean_ctor_set(v___x_129_, 0, v___x_226_);
v___x_230_ = v___x_129_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_221_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_222_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_r_236_; 
v_r_236_ = lean_ctor_get(v_impl_132_, 4);
lean_inc(v_r_236_);
if (lean_obj_tag(v_r_236_) == 0)
{
lean_object* v_k_237_; lean_object* v_v_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_261_; 
v_k_237_ = lean_ctor_get(v_impl_132_, 1);
v_v_238_ = lean_ctor_get(v_impl_132_, 2);
v_isSharedCheck_261_ = !lean_is_exclusive(v_impl_132_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; lean_object* v_unused_263_; lean_object* v_unused_264_; 
v_unused_262_ = lean_ctor_get(v_impl_132_, 4);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_impl_132_, 3);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_impl_132_, 0);
lean_dec(v_unused_264_);
v___x_240_ = v_impl_132_;
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_v_238_);
lean_inc(v_k_237_);
lean_dec(v_impl_132_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_k_242_; lean_object* v_v_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_257_; 
v_k_242_ = lean_ctor_get(v_r_236_, 1);
v_v_243_ = lean_ctor_get(v_r_236_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_r_236_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_258_ = lean_ctor_get(v_r_236_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_r_236_, 3);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_r_236_, 0);
lean_dec(v_unused_260_);
v___x_245_ = v_r_236_;
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_v_243_);
lean_inc(v_k_242_);
lean_dec(v_r_236_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_257_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(3u);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 4, v_l_219_);
lean_ctor_set(v___x_245_, 3, v_l_219_);
lean_ctor_set(v___x_245_, 2, v_v_238_);
lean_ctor_set(v___x_245_, 1, v_k_237_);
lean_ctor_set(v___x_245_, 0, v___x_133_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_l_219_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_l_219_);
v___x_249_ = v_reuseFailAlloc_256_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_251_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 4, v_l_219_);
lean_ctor_set(v___x_240_, 2, v_v_125_);
lean_ctor_set(v___x_240_, 1, v_k_124_);
lean_ctor_set(v___x_240_, 0, v___x_133_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_l_219_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_l_219_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_251_);
lean_ctor_set(v___x_129_, 3, v___x_249_);
lean_ctor_set(v___x_129_, 2, v_v_243_);
lean_ctor_set(v___x_129_, 1, v_k_242_);
lean_ctor_set(v___x_129_, 0, v___x_247_);
v___x_253_ = v___x_129_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_243_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(2u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_236_);
lean_ctor_set(v___x_129_, 3, v_impl_132_);
lean_ctor_set(v___x_129_, 0, v___x_265_);
v___x_267_ = v___x_129_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_impl_132_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_r_236_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
case 1:
{
lean_object* v___x_270_; 
lean_dec(v_v_125_);
lean_dec(v_k_124_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v_v_121_);
lean_ctor_set(v___x_129_, 1, v_k_120_);
v___x_270_ = v___x_129_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_r_127_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
default: 
{
lean_object* v_impl_272_; lean_object* v___x_273_; 
lean_dec(v_size_123_);
v_impl_272_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_120_, v_v_121_, v_r_127_);
v___x_273_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_126_) == 0)
{
lean_object* v_size_274_; lean_object* v_size_275_; lean_object* v_k_276_; lean_object* v_v_277_; lean_object* v_l_278_; lean_object* v_r_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_size_274_ = lean_ctor_get(v_l_126_, 0);
v_size_275_ = lean_ctor_get(v_impl_272_, 0);
lean_inc(v_size_275_);
v_k_276_ = lean_ctor_get(v_impl_272_, 1);
lean_inc(v_k_276_);
v_v_277_ = lean_ctor_get(v_impl_272_, 2);
lean_inc(v_v_277_);
v_l_278_ = lean_ctor_get(v_impl_272_, 3);
lean_inc(v_l_278_);
v_r_279_ = lean_ctor_get(v_impl_272_, 4);
lean_inc(v_r_279_);
v___x_280_ = lean_unsigned_to_nat(3u);
v___x_281_ = lean_nat_mul(v___x_280_, v_size_274_);
v___x_282_ = lean_nat_dec_lt(v___x_281_, v_size_275_);
lean_dec(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_dec(v_r_279_);
lean_dec(v_l_278_);
lean_dec(v_v_277_);
lean_dec(v_k_276_);
v___x_283_ = lean_nat_add(v___x_273_, v_size_274_);
v___x_284_ = lean_nat_add(v___x_283_, v_size_275_);
lean_dec(v_size_275_);
lean_dec(v___x_283_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_impl_272_);
lean_ctor_set(v___x_129_, 0, v___x_284_);
v___x_286_ = v___x_129_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_impl_272_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_351_; 
v_isSharedCheck_351_ = !lean_is_exclusive(v_impl_272_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_352_ = lean_ctor_get(v_impl_272_, 4);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_impl_272_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_272_, 2);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_impl_272_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_272_, 0);
lean_dec(v_unused_356_);
v___x_289_ = v_impl_272_;
v_isShared_290_ = v_isSharedCheck_351_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_impl_272_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_351_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_size_291_; lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v_l_294_; lean_object* v_r_295_; lean_object* v_size_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_size_291_ = lean_ctor_get(v_l_278_, 0);
v_k_292_ = lean_ctor_get(v_l_278_, 1);
v_v_293_ = lean_ctor_get(v_l_278_, 2);
v_l_294_ = lean_ctor_get(v_l_278_, 3);
v_r_295_ = lean_ctor_get(v_l_278_, 4);
v_size_296_ = lean_ctor_get(v_r_279_, 0);
v___x_297_ = lean_unsigned_to_nat(2u);
v___x_298_ = lean_nat_mul(v___x_297_, v_size_296_);
v___x_299_ = lean_nat_dec_lt(v_size_291_, v___x_298_);
lean_dec(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_327_; 
lean_inc(v_r_295_);
lean_inc(v_l_294_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v_isSharedCheck_327_ = !lean_is_exclusive(v_l_278_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_328_ = lean_ctor_get(v_l_278_, 4);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_278_, 3);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_278_, 2);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_278_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_l_278_, 0);
lean_dec(v_unused_332_);
v___x_301_ = v_l_278_;
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
else
{
lean_dec(v_l_278_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_327_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_317_; 
v___x_303_ = lean_nat_add(v___x_273_, v_size_274_);
v___x_304_ = lean_nat_add(v___x_303_, v_size_275_);
lean_dec(v_size_275_);
if (lean_obj_tag(v_l_294_) == 0)
{
lean_object* v_size_325_; 
v_size_325_ = lean_ctor_get(v_l_294_, 0);
lean_inc(v_size_325_);
v___y_317_ = v_size_325_;
goto v___jp_316_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___y_317_ = v___x_326_;
goto v___jp_316_;
}
v___jp_305_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_nat_add(v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 4, v_r_279_);
lean_ctor_set(v___x_301_, 3, v_r_295_);
lean_ctor_set(v___x_301_, 2, v_v_277_);
lean_ctor_set(v___x_301_, 1, v_k_276_);
lean_ctor_set(v___x_301_, 0, v___x_309_);
v___x_311_ = v___x_301_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v_r_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v_r_279_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 4, v___x_311_);
lean_ctor_set(v___x_289_, 3, v___y_306_);
lean_ctor_set(v___x_289_, 2, v_v_293_);
lean_ctor_set(v___x_289_, 1, v_k_292_);
lean_ctor_set(v___x_289_, 0, v___x_304_);
v___x_313_ = v___x_289_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_k_292_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v___y_306_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_nat_add(v___x_303_, v___y_317_);
lean_dec(v___y_317_);
lean_dec(v___x_303_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_l_294_);
lean_ctor_set(v___x_129_, 0, v___x_318_);
v___x_320_ = v___x_129_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_l_294_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_nat_add(v___x_273_, v_size_296_);
if (lean_obj_tag(v_r_295_) == 0)
{
lean_object* v_size_322_; 
v_size_322_ = lean_ctor_get(v_r_295_, 0);
lean_inc(v_size_322_);
v___y_306_ = v___x_320_;
v___y_307_ = v___x_321_;
v___y_308_ = v_size_322_;
goto v___jp_305_;
}
else
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___y_306_ = v___x_320_;
v___y_307_ = v___x_321_;
v___y_308_ = v___x_323_;
goto v___jp_305_;
}
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
lean_del_object(v___x_129_);
v___x_333_ = lean_nat_add(v___x_273_, v_size_274_);
v___x_334_ = lean_nat_add(v___x_333_, v_size_275_);
lean_dec(v_size_275_);
v___x_335_ = lean_nat_add(v___x_333_, v_size_291_);
lean_dec(v___x_333_);
lean_inc_ref(v_l_126_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 4, v_l_278_);
lean_ctor_set(v___x_289_, 3, v_l_126_);
lean_ctor_set(v___x_289_, 2, v_v_125_);
lean_ctor_set(v___x_289_, 1, v_k_124_);
lean_ctor_set(v___x_289_, 0, v___x_335_);
v___x_337_ = v___x_289_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_l_126_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_l_278_);
v___x_337_ = v_reuseFailAlloc_350_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_isSharedCheck_344_ = !lean_is_exclusive(v_l_126_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; lean_object* v_unused_348_; lean_object* v_unused_349_; 
v_unused_345_ = lean_ctor_get(v_l_126_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_l_126_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_l_126_, 2);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_l_126_, 1);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_l_126_, 0);
lean_dec(v_unused_349_);
v___x_339_ = v_l_126_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_l_126_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_r_279_);
lean_ctor_set(v___x_339_, 3, v___x_337_);
lean_ctor_set(v___x_339_, 2, v_v_277_);
lean_ctor_set(v___x_339_, 1, v_k_276_);
lean_ctor_set(v___x_339_, 0, v___x_334_);
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v_r_279_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_357_; 
v_l_357_ = lean_ctor_get(v_impl_272_, 3);
lean_inc(v_l_357_);
if (lean_obj_tag(v_l_357_) == 0)
{
lean_object* v_r_358_; lean_object* v_k_359_; lean_object* v_v_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_383_; 
v_r_358_ = lean_ctor_get(v_impl_272_, 4);
v_k_359_ = lean_ctor_get(v_impl_272_, 1);
v_v_360_ = lean_ctor_get(v_impl_272_, 2);
v_isSharedCheck_383_ = !lean_is_exclusive(v_impl_272_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_384_ = lean_ctor_get(v_impl_272_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_impl_272_, 0);
lean_dec(v_unused_385_);
v___x_362_ = v_impl_272_;
v_isShared_363_ = v_isSharedCheck_383_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_r_358_);
lean_inc(v_v_360_);
lean_inc(v_k_359_);
lean_dec(v_impl_272_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_383_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_k_364_; lean_object* v_v_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_379_; 
v_k_364_ = lean_ctor_get(v_l_357_, 1);
v_v_365_ = lean_ctor_get(v_l_357_, 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_l_357_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; 
v_unused_380_ = lean_ctor_get(v_l_357_, 4);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_l_357_, 3);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_l_357_, 0);
lean_dec(v_unused_382_);
v___x_367_ = v_l_357_;
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_v_365_);
lean_inc(v_k_364_);
lean_dec(v_l_357_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_379_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_358_, 2);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 4, v_r_358_);
lean_ctor_set(v___x_367_, 3, v_r_358_);
lean_ctor_set(v___x_367_, 2, v_v_125_);
lean_ctor_set(v___x_367_, 1, v_k_124_);
lean_ctor_set(v___x_367_, 0, v___x_273_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_r_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_r_358_);
v___x_371_ = v_reuseFailAlloc_378_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
lean_inc(v_r_358_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 3, v_r_358_);
lean_ctor_set(v___x_362_, 0, v___x_273_);
v___x_373_ = v___x_362_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_359_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_360_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_r_358_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_r_358_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_373_);
lean_ctor_set(v___x_129_, 3, v___x_371_);
lean_ctor_set(v___x_129_, 2, v_v_365_);
lean_ctor_set(v___x_129_, 1, v_k_364_);
lean_ctor_set(v___x_129_, 0, v___x_369_);
v___x_375_ = v___x_129_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_v_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
else
{
lean_object* v_r_386_; 
v_r_386_ = lean_ctor_get(v_impl_272_, 4);
lean_inc(v_r_386_);
if (lean_obj_tag(v_r_386_) == 0)
{
lean_object* v_k_387_; lean_object* v_v_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_399_; 
v_k_387_ = lean_ctor_get(v_impl_272_, 1);
v_v_388_ = lean_ctor_get(v_impl_272_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_impl_272_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_400_ = lean_ctor_get(v_impl_272_, 4);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_impl_272_, 3);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_impl_272_, 0);
lean_dec(v_unused_402_);
v___x_390_ = v_impl_272_;
v_isShared_391_ = v_isSharedCheck_399_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_v_388_);
lean_inc(v_k_387_);
lean_dec(v_impl_272_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_399_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_unsigned_to_nat(3u);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 4, v_l_357_);
lean_ctor_set(v___x_390_, 2, v_v_125_);
lean_ctor_set(v___x_390_, 1, v_k_124_);
lean_ctor_set(v___x_390_, 0, v___x_273_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_l_357_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_l_357_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_r_386_);
lean_ctor_set(v___x_129_, 3, v___x_394_);
lean_ctor_set(v___x_129_, 2, v_v_388_);
lean_ctor_set(v___x_129_, 1, v_k_387_);
lean_ctor_set(v___x_129_, 0, v___x_392_);
v___x_396_ = v___x_129_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_387_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_388_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_r_386_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(2u);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v_impl_272_);
lean_ctor_set(v___x_129_, 3, v_r_386_);
lean_ctor_set(v___x_129_, 0, v___x_403_);
v___x_405_ = v___x_129_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_r_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_impl_272_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_k_120_);
lean_ctor_set(v___x_409_, 2, v_v_121_);
lean_ctor_set(v___x_409_, 3, v_t_122_);
lean_ctor_set(v___x_409_, 4, v_t_122_);
return v___x_409_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object* v_k_410_, lean_object* v_t_411_){
_start:
{
if (lean_obj_tag(v_t_411_) == 0)
{
lean_object* v_k_412_; lean_object* v_l_413_; lean_object* v_r_414_; uint8_t v___x_415_; 
v_k_412_ = lean_ctor_get(v_t_411_, 1);
v_l_413_ = lean_ctor_get(v_t_411_, 3);
v_r_414_ = lean_ctor_get(v_t_411_, 4);
v___x_415_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_410_, v_k_412_);
switch(v___x_415_)
{
case 0:
{
v_t_411_ = v_l_413_;
goto _start;
}
case 1:
{
uint8_t v___x_417_; 
v___x_417_ = 1;
return v___x_417_;
}
default: 
{
v_t_411_ = v_r_414_;
goto _start;
}
}
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object* v_k_420_, lean_object* v_t_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_420_, v_t_421_);
lean_dec(v_t_421_);
lean_dec(v_k_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* v_x_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
switch(lean_obj_tag(v_x_424_))
{
case 0:
{
lean_object* v_e_427_; lean_object* v_b_428_; lean_object* v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v_f_442_; lean_object* v___y_443_; lean_object* v___y_444_; 
v_e_427_ = lean_ctor_get(v_x_424_, 2);
lean_inc_ref(v_e_427_);
v_b_428_ = lean_ctor_get(v_x_424_, 3);
lean_inc(v_b_428_);
lean_dec_ref(v_x_424_);
switch(lean_obj_tag(v_e_427_))
{
case 6:
{
lean_object* v_c_452_; 
v_c_452_ = lean_ctor_get(v_e_427_, 0);
lean_inc(v_c_452_);
lean_dec_ref(v_e_427_);
v_f_442_ = v_c_452_;
v___y_443_ = v_a_425_;
v___y_444_ = v_a_426_;
goto v___jp_441_;
}
case 7:
{
lean_object* v_c_453_; 
v_c_453_ = lean_ctor_get(v_e_427_, 0);
lean_inc(v_c_453_);
lean_dec_ref(v_e_427_);
v_f_442_ = v_c_453_;
v___y_443_ = v_a_425_;
v___y_444_ = v_a_426_;
goto v___jp_441_;
}
default: 
{
lean_dec_ref(v_e_427_);
v_x_424_ = v_b_428_;
goto _start;
}
}
v___jp_429_:
{
uint8_t v___x_435_; 
v___x_435_ = lean_unbox(v_fst_433_);
lean_dec(v_fst_433_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_array_push(v___y_430_, v___y_431_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_snd_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v_x_424_ = v_b_428_;
v_a_425_ = v___y_432_;
v_a_426_ = v___x_437_;
goto _start;
}
else
{
lean_object* v___x_439_; 
lean_dec(v___y_431_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_snd_434_);
lean_ctor_set(v___x_439_, 1, v___y_430_);
v_x_424_ = v_b_428_;
v_a_425_ = v___y_432_;
v_a_426_ = v___x_439_;
goto _start;
}
}
v___jp_441_:
{
lean_object* v_set_445_; lean_object* v_order_446_; uint8_t v___x_447_; 
v_set_445_ = lean_ctor_get(v___y_444_, 0);
lean_inc(v_set_445_);
v_order_446_ = lean_ctor_get(v___y_444_, 1);
lean_inc_ref(v_order_446_);
lean_dec_ref(v___y_444_);
v___x_447_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_f_442_, v_set_445_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_box(0);
lean_inc(v_f_442_);
v___x_449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_f_442_, v___x_448_, v_set_445_);
v___x_450_ = lean_box(v___x_447_);
v___y_430_ = v_order_446_;
v___y_431_ = v_f_442_;
v___y_432_ = v___y_443_;
v_fst_433_ = v___x_450_;
v_snd_434_ = v___x_449_;
goto v___jp_429_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_box(v___x_447_);
v___y_430_ = v_order_446_;
v___y_431_ = v_f_442_;
v___y_432_ = v___y_443_;
v_fst_433_ = v___x_451_;
v_snd_434_ = v_set_445_;
goto v___jp_429_;
}
}
}
case 1:
{
lean_object* v_v_455_; lean_object* v_b_456_; lean_object* v___x_457_; lean_object* v_snd_458_; 
v_v_455_ = lean_ctor_get(v_x_424_, 2);
lean_inc(v_v_455_);
v_b_456_ = lean_ctor_get(v_x_424_, 3);
lean_inc(v_b_456_);
lean_dec_ref(v_x_424_);
v___x_457_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_455_, v_a_425_, v_a_426_);
v_snd_458_ = lean_ctor_get(v___x_457_, 1);
lean_inc(v_snd_458_);
lean_dec_ref(v___x_457_);
v_x_424_ = v_b_456_;
v_a_426_ = v_snd_458_;
goto _start;
}
case 9:
{
lean_object* v_cs_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_cs_460_ = lean_ctor_get(v_x_424_, 3);
lean_inc_ref(v_cs_460_);
lean_dec_ref(v_x_424_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_array_get_size(v_cs_460_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec_ref(v_cs_460_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v_a_426_);
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = lean_nat_dec_le(v___x_462_, v___x_462_);
if (v___x_466_ == 0)
{
if (v___x_464_ == 0)
{
lean_object* v___x_467_; 
lean_dec_ref(v_cs_460_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_463_);
lean_ctor_set(v___x_467_, 1, v_a_426_);
return v___x_467_;
}
else
{
size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; 
v___x_468_ = ((size_t)0ULL);
v___x_469_ = lean_usize_of_nat(v___x_462_);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_460_, v___x_468_, v___x_469_, v___x_463_, v_a_425_, v_a_426_);
lean_dec_ref(v_cs_460_);
return v___x_470_;
}
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((size_t)0ULL);
v___x_472_ = lean_usize_of_nat(v___x_462_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_460_, v___x_471_, v___x_472_, v___x_463_, v_a_425_, v_a_426_);
lean_dec_ref(v_cs_460_);
return v___x_473_;
}
}
}
default: 
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_IR_FnBody_isTerminal(v_x_424_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_IR_FnBody_body(v_x_424_);
lean_dec(v_x_424_);
v_x_424_ = v___x_475_;
goto _start;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_x_424_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_a_426_);
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object* v_as_479_, size_t v_i_480_, size_t v_stop_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = lean_usize_dec_eq(v_i_480_, v_stop_481_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_fst_489_; lean_object* v_snd_490_; size_t v___x_491_; size_t v___x_492_; 
v___x_486_ = lean_array_uget_borrowed(v_as_479_, v_i_480_);
v___x_487_ = l_Lean_IR_Alt_body(v___x_486_);
v___x_488_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v___x_487_, v___y_483_, v___y_484_);
v_fst_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_fst_489_);
v_snd_490_ = lean_ctor_get(v___x_488_, 1);
lean_inc(v_snd_490_);
lean_dec_ref(v___x_488_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_480_, v___x_491_);
v_i_480_ = v___x_492_;
v_b_482_ = v_fst_489_;
v___y_484_ = v_snd_490_;
goto _start;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v_b_482_);
lean_ctor_set(v___x_494_, 1, v___y_484_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object* v_as_495_, lean_object* v_i_496_, lean_object* v_stop_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
size_t v_i_boxed_501_; size_t v_stop_boxed_502_; lean_object* v_res_503_; 
v_i_boxed_501_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_stop_boxed_502_ = lean_unbox_usize(v_stop_497_);
lean_dec(v_stop_497_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_495_, v_i_boxed_501_, v_stop_boxed_502_, v_b_498_, v___y_499_, v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_as_495_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* v_x_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_504_, v_a_505_, v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_507_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object* v_00_u03b2_508_, lean_object* v_k_509_, lean_object* v_t_510_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_509_, v_t_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_512_, lean_object* v_k_513_, lean_object* v_t_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_512_, v_k_513_, v_t_514_);
lean_dec(v_t_514_);
lean_dec(v_k_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object* v_00_u03b2_517_, lean_object* v_k_518_, lean_object* v_v_519_, lean_object* v_t_520_, lean_object* v_hl_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_518_, v_v_519_, v_t_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* v_fn_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_get_init_fn_name_for(v_a_524_, v_fn_523_);
if (lean_obj_tag(v___x_526_) == 1)
{
lean_object* v_val_527_; lean_object* v_set_528_; lean_object* v_order_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_551_; 
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref(v___x_526_);
v_set_528_ = lean_ctor_get(v_a_525_, 0);
v_order_529_ = lean_ctor_get(v_a_525_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_551_ == 0)
{
v___x_531_ = v_a_525_;
v_isShared_532_ = v_isSharedCheck_551_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_order_529_);
lean_inc(v_set_528_);
lean_dec(v_a_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_551_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v_fst_535_; lean_object* v_snd_536_; uint8_t v___x_547_; 
v___x_533_ = lean_box(0);
v___x_547_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_527_, v_set_528_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_inc(v_val_527_);
v___x_548_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_527_, v___x_533_, v_set_528_);
v___x_549_ = lean_box(v___x_547_);
v_fst_535_ = v___x_549_;
v_snd_536_ = v___x_548_;
goto v___jp_534_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = lean_box(v___x_547_);
v_fst_535_ = v___x_550_;
v_snd_536_ = v_set_528_;
goto v___jp_534_;
}
v___jp_534_:
{
uint8_t v___x_537_; 
v___x_537_ = lean_unbox(v_fst_535_);
lean_dec(v_fst_535_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_array_push(v_order_529_, v_val_527_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_538_);
lean_ctor_set(v___x_531_, 0, v_snd_536_);
v___x_540_ = v___x_531_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_snd_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_533_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
}
else
{
lean_object* v___x_544_; 
lean_dec(v_val_527_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v_snd_536_);
v___x_544_ = v___x_531_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_snd_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_order_529_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_533_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
return v___x_545_;
}
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_526_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_525_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v_f_557_; lean_object* v_body_558_; lean_object* v___x_559_; lean_object* v_snd_560_; lean_object* v___x_561_; 
v_f_557_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_f_557_);
v_body_558_ = lean_ctor_get(v_x_554_, 3);
lean_inc(v_body_558_);
lean_dec_ref(v_x_554_);
lean_inc_ref(v_a_555_);
v___x_559_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_557_, v_a_555_, v_a_556_);
v_snd_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_snd_560_);
lean_dec_ref(v___x_559_);
v___x_561_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_558_, v_a_555_, v_snd_560_);
lean_dec_ref(v_a_555_);
return v___x_561_;
}
else
{
lean_object* v_f_562_; lean_object* v___x_563_; 
v_f_562_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_f_562_);
lean_dec_ref(v_x_554_);
v___x_563_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_562_, v_a_555_, v_a_556_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
if (lean_obj_tag(v_as_564_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v___y_565_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___y_566_);
return v___x_568_;
}
else
{
lean_object* v_head_569_; lean_object* v_tail_570_; lean_object* v___x_571_; lean_object* v_snd_572_; lean_object* v_set_573_; lean_object* v_order_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_597_; 
v_head_569_ = lean_ctor_get(v_as_564_, 0);
lean_inc(v_head_569_);
v_tail_570_ = lean_ctor_get(v_as_564_, 1);
lean_inc(v_tail_570_);
lean_dec_ref(v_as_564_);
lean_inc_ref(v___y_565_);
lean_inc(v_head_569_);
v___x_571_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_569_, v___y_565_, v___y_566_);
v_snd_572_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_571_);
v_set_573_ = lean_ctor_get(v_snd_572_, 0);
v_order_574_ = lean_ctor_get(v_snd_572_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_snd_572_);
if (v_isSharedCheck_597_ == 0)
{
v___x_576_ = v_snd_572_;
v_isShared_577_ = v_isSharedCheck_597_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_order_574_);
lean_inc(v_set_573_);
lean_dec(v_snd_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_597_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v_fst_580_; lean_object* v_snd_581_; uint8_t v___x_592_; 
v___x_578_ = l_Lean_IR_Decl_name(v_head_569_);
lean_dec(v_head_569_);
v___x_592_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_578_, v_set_573_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_box(0);
lean_inc(v___x_578_);
v___x_594_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_578_, v___x_593_, v_set_573_);
v___x_595_ = lean_box(v___x_592_);
v_fst_580_ = v___x_595_;
v_snd_581_ = v___x_594_;
goto v___jp_579_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_box(v___x_592_);
v_fst_580_ = v___x_596_;
v_snd_581_ = v_set_573_;
goto v___jp_579_;
}
v___jp_579_:
{
uint8_t v___x_582_; 
v___x_582_ = lean_unbox(v_fst_580_);
lean_dec(v_fst_580_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_array_push(v_order_574_, v___x_578_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v___x_583_);
lean_ctor_set(v___x_576_, 0, v_snd_581_);
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_snd_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
v_as_564_ = v_tail_570_;
v___y_566_ = v___x_585_;
goto _start;
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v___x_578_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v_snd_581_);
v___x_589_ = v___x_576_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_snd_581_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_order_574_);
v___x_589_ = v_reuseFailAlloc_591_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
v_as_564_ = v_tail_570_;
v___y_566_ = v___x_589_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_598_, v_a_599_, v_a_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_605_ = l_Lean_NameSet_empty;
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_607_, lean_object* v_decls_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_snd_611_; lean_object* v_order_612_; 
v___x_609_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_610_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_608_, v_env_607_, v___x_609_);
v_snd_611_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_snd_611_);
lean_dec_ref(v___x_610_);
v_order_612_ = lean_ctor_get(v_snd_611_, 1);
lean_inc_ref(v_order_612_);
lean_dec(v_snd_611_);
return v_order_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_615_, lean_object* v_t_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_629_; 
v_fst_618_ = lean_ctor_get(v_x_617_, 0);
v_snd_619_ = lean_ctor_get(v_x_617_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_617_);
if (v_isSharedCheck_629_ == 0)
{
v___x_621_ = v_x_617_;
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_inc(v_fst_618_);
lean_dec(v_x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_629_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_623_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_624_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_623_, v___x_624_, v_fst_618_, v_x_615_, v_t_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_625_);
v___x_627_ = v___x_621_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_snd_619_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
return v_x_630_;
}
else
{
lean_object* v_key_632_; lean_object* v_value_633_; lean_object* v_tail_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_657_; 
v_key_632_ = lean_ctor_get(v_x_631_, 0);
v_value_633_ = lean_ctor_get(v_x_631_, 1);
v_tail_634_ = lean_ctor_get(v_x_631_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_657_ == 0)
{
v___x_636_ = v_x_631_;
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_tail_634_);
lean_inc(v_value_633_);
lean_inc(v_key_632_);
lean_dec(v_x_631_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; uint64_t v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v_fold_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_638_ = lean_array_get_size(v_x_630_);
v___x_639_ = l_Lean_IR_instHashableVarId_hash(v_key_632_);
v___x_640_ = 32ULL;
v___x_641_ = lean_uint64_shift_right(v___x_639_, v___x_640_);
v_fold_642_ = lean_uint64_xor(v___x_639_, v___x_641_);
v___x_643_ = 16ULL;
v___x_644_ = lean_uint64_shift_right(v_fold_642_, v___x_643_);
v___x_645_ = lean_uint64_xor(v_fold_642_, v___x_644_);
v___x_646_ = lean_uint64_to_usize(v___x_645_);
v___x_647_ = lean_usize_of_nat(v___x_638_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_sub(v___x_647_, v___x_648_);
v___x_650_ = lean_usize_land(v___x_646_, v___x_649_);
v___x_651_ = lean_array_uget_borrowed(v_x_630_, v___x_650_);
lean_inc(v___x_651_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v___x_651_);
v___x_653_ = v___x_636_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_key_632_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_value_633_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v___x_651_);
v___x_653_ = v_reuseFailAlloc_656_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; 
v___x_654_ = lean_array_uset(v_x_630_, v___x_650_, v___x_653_);
v_x_630_ = v___x_654_;
v_x_631_ = v_tail_634_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_658_, lean_object* v_source_659_, lean_object* v_target_660_){
_start:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_array_get_size(v_source_659_);
v___x_662_ = lean_nat_dec_lt(v_i_658_, v___x_661_);
if (v___x_662_ == 0)
{
lean_dec_ref(v_source_659_);
lean_dec(v_i_658_);
return v_target_660_;
}
else
{
lean_object* v_es_663_; lean_object* v___x_664_; lean_object* v_source_665_; lean_object* v_target_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_es_663_ = lean_array_fget(v_source_659_, v_i_658_);
v___x_664_ = lean_box(0);
v_source_665_ = lean_array_fset(v_source_659_, v_i_658_, v___x_664_);
v_target_666_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_660_, v_es_663_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_i_658_, v___x_667_);
lean_dec(v_i_658_);
v_i_658_ = v___x_668_;
v_source_659_ = v_source_665_;
v_target_660_ = v_target_666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_nbuckets_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_671_ = lean_array_get_size(v_data_670_);
v___x_672_ = lean_unsigned_to_nat(2u);
v_nbuckets_673_ = lean_nat_mul(v___x_671_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_box(0);
v___x_676_ = lean_mk_array(v_nbuckets_673_, v___x_675_);
v___x_677_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_674_, v_data_670_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 0;
return v___x_680_;
}
else
{
lean_object* v_key_681_; lean_object* v_tail_682_; uint8_t v___x_683_; 
v_key_681_ = lean_ctor_get(v_x_679_, 0);
v_tail_682_ = lean_ctor_get(v_x_679_, 2);
v___x_683_ = l_Lean_IR_instBEqVarId_beq(v_key_681_, v_a_678_);
if (v___x_683_ == 0)
{
v_x_679_ = v_tail_682_;
goto _start;
}
else
{
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_685_, lean_object* v_x_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_685_, v_x_686_);
lean_dec(v_x_686_);
lean_dec(v_a_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_689_, lean_object* v_b_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_dec(v_b_690_);
lean_dec(v_a_689_);
return v_x_691_;
}
else
{
lean_object* v_key_692_; lean_object* v_value_693_; lean_object* v_tail_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_706_; 
v_key_692_ = lean_ctor_get(v_x_691_, 0);
v_value_693_ = lean_ctor_get(v_x_691_, 1);
v_tail_694_ = lean_ctor_get(v_x_691_, 2);
v_isSharedCheck_706_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_706_ == 0)
{
v___x_696_ = v_x_691_;
v_isShared_697_ = v_isSharedCheck_706_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_tail_694_);
lean_inc(v_value_693_);
lean_inc(v_key_692_);
lean_dec(v_x_691_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_706_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_IR_instBEqVarId_beq(v_key_692_, v_a_689_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_689_, v_b_690_, v_tail_694_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 2, v___x_699_);
v___x_701_ = v___x_696_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_key_692_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_value_693_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v_value_693_);
lean_dec(v_key_692_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_b_690_);
lean_ctor_set(v___x_696_, 0, v_a_689_);
v___x_704_ = v___x_696_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_689_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_b_690_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_tail_694_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_707_, lean_object* v_a_708_, lean_object* v_b_709_){
_start:
{
lean_object* v_size_710_; lean_object* v_buckets_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_754_; 
v_size_710_ = lean_ctor_get(v_m_707_, 0);
v_buckets_711_ = lean_ctor_get(v_m_707_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_m_707_);
if (v_isSharedCheck_754_ == 0)
{
v___x_713_ = v_m_707_;
v_isShared_714_ = v_isSharedCheck_754_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_buckets_711_);
lean_inc(v_size_710_);
lean_dec(v_m_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_754_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v___x_718_; uint64_t v_fold_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v_bkt_728_; uint8_t v___x_729_; 
v___x_715_ = lean_array_get_size(v_buckets_711_);
v___x_716_ = l_Lean_IR_instHashableVarId_hash(v_a_708_);
v___x_717_ = 32ULL;
v___x_718_ = lean_uint64_shift_right(v___x_716_, v___x_717_);
v_fold_719_ = lean_uint64_xor(v___x_716_, v___x_718_);
v___x_720_ = 16ULL;
v___x_721_ = lean_uint64_shift_right(v_fold_719_, v___x_720_);
v___x_722_ = lean_uint64_xor(v_fold_719_, v___x_721_);
v___x_723_ = lean_uint64_to_usize(v___x_722_);
v___x_724_ = lean_usize_of_nat(v___x_715_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_sub(v___x_724_, v___x_725_);
v___x_727_ = lean_usize_land(v___x_723_, v___x_726_);
v_bkt_728_ = lean_array_uget_borrowed(v_buckets_711_, v___x_727_);
v___x_729_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_708_, v_bkt_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v_size_x27_731_; lean_object* v___x_732_; lean_object* v_buckets_x27_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v_size_x27_731_ = lean_nat_add(v_size_710_, v___x_730_);
lean_dec(v_size_710_);
lean_inc(v_bkt_728_);
v___x_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_732_, 0, v_a_708_);
lean_ctor_set(v___x_732_, 1, v_b_709_);
lean_ctor_set(v___x_732_, 2, v_bkt_728_);
v_buckets_x27_733_ = lean_array_uset(v_buckets_711_, v___x_727_, v___x_732_);
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = lean_nat_mul(v_size_x27_731_, v___x_734_);
v___x_736_ = lean_unsigned_to_nat(3u);
v___x_737_ = lean_nat_div(v___x_735_, v___x_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_array_get_size(v_buckets_x27_733_);
v___x_739_ = lean_nat_dec_le(v___x_737_, v___x_738_);
lean_dec(v___x_737_);
if (v___x_739_ == 0)
{
lean_object* v_val_740_; lean_object* v___x_742_; 
v_val_740_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_733_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v_val_740_);
lean_ctor_set(v___x_713_, 0, v_size_x27_731_);
v___x_742_ = v___x_713_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_size_x27_731_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_val_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v___x_745_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v_buckets_x27_733_);
lean_ctor_set(v___x_713_, 0, v_size_x27_731_);
v___x_745_ = v___x_713_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_size_x27_731_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_buckets_x27_733_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v___x_747_; lean_object* v_buckets_x27_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_inc(v_bkt_728_);
v___x_747_ = lean_box(0);
v_buckets_x27_748_ = lean_array_uset(v_buckets_711_, v___x_727_, v___x_747_);
v___x_749_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_708_, v_b_709_, v_bkt_728_);
v___x_750_ = lean_array_uset(v_buckets_x27_748_, v___x_727_, v___x_749_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_750_);
v___x_752_ = v___x_713_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_size_710_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_755_, size_t v_i_756_, size_t v_stop_757_, lean_object* v_b_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = lean_usize_dec_eq(v_i_756_, v_stop_757_);
if (v___x_759_ == 0)
{
lean_object* v_fst_760_; lean_object* v_snd_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_775_; 
v_fst_760_ = lean_ctor_get(v_b_758_, 0);
v_snd_761_ = lean_ctor_get(v_b_758_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_b_758_);
if (v_isSharedCheck_775_ == 0)
{
v___x_763_ = v_b_758_;
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snd_761_);
lean_inc(v_fst_760_);
lean_dec(v_b_758_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v_x_766_; lean_object* v_ty_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_765_ = lean_array_uget_borrowed(v_as_755_, v_i_756_);
v_x_766_ = lean_ctor_get(v___x_765_, 0);
v_ty_767_ = lean_ctor_get(v___x_765_, 1);
lean_inc(v_ty_767_);
lean_inc(v_x_766_);
v___x_768_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_760_, v_x_766_, v_ty_767_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_768_);
v___x_770_ = v___x_763_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_snd_761_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
size_t v___x_771_; size_t v___x_772_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_756_, v___x_771_);
v_i_756_ = v___x_772_;
v_b_758_ = v___x_770_;
goto _start;
}
}
}
else
{
return v_b_758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_stop_778_, lean_object* v_b_779_){
_start:
{
size_t v_i_boxed_780_; size_t v_stop_boxed_781_; lean_object* v_res_782_; 
v_i_boxed_780_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_stop_boxed_781_ = lean_unbox_usize(v_stop_778_);
lean_dec(v_stop_778_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_776_, v_i_boxed_780_, v_stop_boxed_781_, v_b_779_);
lean_dec_ref(v_as_776_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_783_, lean_object* v_s_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_array_get_size(v_ps_783_);
v___x_787_ = lean_nat_dec_lt(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
return v_s_784_;
}
else
{
uint8_t v___x_788_; 
v___x_788_ = lean_nat_dec_le(v___x_786_, v___x_786_);
if (v___x_788_ == 0)
{
if (v___x_787_ == 0)
{
return v_s_784_;
}
else
{
size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((size_t)0ULL);
v___x_790_ = lean_usize_of_nat(v___x_786_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_783_, v___x_789_, v___x_790_, v_s_784_);
return v___x_791_;
}
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_of_nat(v___x_786_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_783_, v___x_792_, v___x_793_, v_s_784_);
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_795_, lean_object* v_s_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_IR_CollectMaps_collectParams(v_ps_795_, v_s_796_);
lean_dec_ref(v_ps_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_798_, lean_object* v_m_799_, lean_object* v_a_800_, lean_object* v_b_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_799_, v_a_800_, v_b_801_);
return v___x_802_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_803_, lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_807_, lean_object* v_a_808_, lean_object* v_x_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_807_, v_a_808_, v_x_809_);
lean_dec(v_x_809_);
lean_dec(v_a_808_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_812_, lean_object* v_data_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_b_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_816_, v_b_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_820_, lean_object* v_i_821_, lean_object* v_source_822_, lean_object* v_target_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_821_, v_source_822_, v_target_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_831_, lean_object* v_xs_832_, lean_object* v_x_833_){
_start:
{
lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
v_fst_834_ = lean_ctor_get(v_x_833_, 0);
v_snd_835_ = lean_ctor_get(v_x_833_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_x_833_);
if (v_isSharedCheck_845_ == 0)
{
v___x_837_ = v_x_833_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_snd_835_);
lean_inc(v_fst_834_);
lean_dec(v_x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_839_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_840_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_839_, v___x_840_, v_snd_835_, v_j_831_, v_xs_832_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_841_);
v___x_843_ = v___x_837_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_846_, lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
uint8_t v___x_848_; 
v___x_848_ = 0;
return v___x_848_;
}
else
{
lean_object* v_key_849_; lean_object* v_tail_850_; uint8_t v___x_851_; 
v_key_849_ = lean_ctor_get(v_x_847_, 0);
v_tail_850_ = lean_ctor_get(v_x_847_, 2);
v___x_851_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_849_, v_a_846_);
if (v___x_851_ == 0)
{
v_x_847_ = v_tail_850_;
goto _start;
}
else
{
return v___x_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_853_, v_x_854_);
lean_dec(v_x_854_);
lean_dec(v_a_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_857_, lean_object* v_x_858_){
_start:
{
if (lean_obj_tag(v_x_858_) == 0)
{
return v_x_857_;
}
else
{
lean_object* v_key_859_; lean_object* v_value_860_; lean_object* v_tail_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_884_; 
v_key_859_ = lean_ctor_get(v_x_858_, 0);
v_value_860_ = lean_ctor_get(v_x_858_, 1);
v_tail_861_ = lean_ctor_get(v_x_858_, 2);
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_858_);
if (v_isSharedCheck_884_ == 0)
{
v___x_863_ = v_x_858_;
v_isShared_864_ = v_isSharedCheck_884_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_tail_861_);
lean_inc(v_value_860_);
lean_inc(v_key_859_);
lean_dec(v_x_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_884_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint64_t v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v_fold_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_865_ = lean_array_get_size(v_x_857_);
v___x_866_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_859_);
v___x_867_ = 32ULL;
v___x_868_ = lean_uint64_shift_right(v___x_866_, v___x_867_);
v_fold_869_ = lean_uint64_xor(v___x_866_, v___x_868_);
v___x_870_ = 16ULL;
v___x_871_ = lean_uint64_shift_right(v_fold_869_, v___x_870_);
v___x_872_ = lean_uint64_xor(v_fold_869_, v___x_871_);
v___x_873_ = lean_uint64_to_usize(v___x_872_);
v___x_874_ = lean_usize_of_nat(v___x_865_);
v___x_875_ = ((size_t)1ULL);
v___x_876_ = lean_usize_sub(v___x_874_, v___x_875_);
v___x_877_ = lean_usize_land(v___x_873_, v___x_876_);
v___x_878_ = lean_array_uget_borrowed(v_x_857_, v___x_877_);
lean_inc(v___x_878_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 2, v___x_878_);
v___x_880_ = v___x_863_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_key_859_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_value_860_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v___x_878_);
v___x_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = lean_array_uset(v_x_857_, v___x_877_, v___x_880_);
v_x_857_ = v___x_881_;
v_x_858_ = v_tail_861_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_885_, lean_object* v_source_886_, lean_object* v_target_887_){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_array_get_size(v_source_886_);
v___x_889_ = lean_nat_dec_lt(v_i_885_, v___x_888_);
if (v___x_889_ == 0)
{
lean_dec_ref(v_source_886_);
lean_dec(v_i_885_);
return v_target_887_;
}
else
{
lean_object* v_es_890_; lean_object* v___x_891_; lean_object* v_source_892_; lean_object* v_target_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_es_890_ = lean_array_fget(v_source_886_, v_i_885_);
v___x_891_ = lean_box(0);
v_source_892_ = lean_array_fset(v_source_886_, v_i_885_, v___x_891_);
v_target_893_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_887_, v_es_890_);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_nat_add(v_i_885_, v___x_894_);
lean_dec(v_i_885_);
v_i_885_ = v___x_895_;
v_source_886_ = v_source_892_;
v_target_887_ = v_target_893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_nbuckets_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_898_ = lean_array_get_size(v_data_897_);
v___x_899_ = lean_unsigned_to_nat(2u);
v_nbuckets_900_ = lean_nat_mul(v___x_898_, v___x_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_box(0);
v___x_903_ = lean_mk_array(v_nbuckets_900_, v___x_902_);
v___x_904_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_901_, v_data_897_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_905_, lean_object* v_b_906_, lean_object* v_x_907_){
_start:
{
if (lean_obj_tag(v_x_907_) == 0)
{
lean_dec(v_b_906_);
lean_dec(v_a_905_);
return v_x_907_;
}
else
{
lean_object* v_key_908_; lean_object* v_value_909_; lean_object* v_tail_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v_key_908_ = lean_ctor_get(v_x_907_, 0);
v_value_909_ = lean_ctor_get(v_x_907_, 1);
v_tail_910_ = lean_ctor_get(v_x_907_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_922_ == 0)
{
v___x_912_ = v_x_907_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_tail_910_);
lean_inc(v_value_909_);
lean_inc(v_key_908_);
lean_dec(v_x_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_908_, v_a_905_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_905_, v_b_906_, v_tail_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 2, v___x_915_);
v___x_917_ = v___x_912_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_key_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_value_909_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v_value_909_);
lean_dec(v_key_908_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_b_906_);
lean_ctor_set(v___x_912_, 0, v_a_905_);
v___x_920_ = v___x_912_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_b_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_tail_910_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_923_, lean_object* v_a_924_, lean_object* v_b_925_){
_start:
{
lean_object* v_size_926_; lean_object* v_buckets_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_970_; 
v_size_926_ = lean_ctor_get(v_m_923_, 0);
v_buckets_927_ = lean_ctor_get(v_m_923_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_m_923_);
if (v_isSharedCheck_970_ == 0)
{
v___x_929_ = v_m_923_;
v_isShared_930_ = v_isSharedCheck_970_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_buckets_927_);
lean_inc(v_size_926_);
lean_dec(v_m_923_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_970_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; uint64_t v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v_fold_935_; uint64_t v___x_936_; uint64_t v___x_937_; uint64_t v___x_938_; size_t v___x_939_; size_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v_bkt_944_; uint8_t v___x_945_; 
v___x_931_ = lean_array_get_size(v_buckets_927_);
v___x_932_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_924_);
v___x_933_ = 32ULL;
v___x_934_ = lean_uint64_shift_right(v___x_932_, v___x_933_);
v_fold_935_ = lean_uint64_xor(v___x_932_, v___x_934_);
v___x_936_ = 16ULL;
v___x_937_ = lean_uint64_shift_right(v_fold_935_, v___x_936_);
v___x_938_ = lean_uint64_xor(v_fold_935_, v___x_937_);
v___x_939_ = lean_uint64_to_usize(v___x_938_);
v___x_940_ = lean_usize_of_nat(v___x_931_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_sub(v___x_940_, v___x_941_);
v___x_943_ = lean_usize_land(v___x_939_, v___x_942_);
v_bkt_944_ = lean_array_uget_borrowed(v_buckets_927_, v___x_943_);
v___x_945_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_924_, v_bkt_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v_size_x27_947_; lean_object* v___x_948_; lean_object* v_buckets_x27_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v_size_x27_947_ = lean_nat_add(v_size_926_, v___x_946_);
lean_dec(v_size_926_);
lean_inc(v_bkt_944_);
v___x_948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_948_, 0, v_a_924_);
lean_ctor_set(v___x_948_, 1, v_b_925_);
lean_ctor_set(v___x_948_, 2, v_bkt_944_);
v_buckets_x27_949_ = lean_array_uset(v_buckets_927_, v___x_943_, v___x_948_);
v___x_950_ = lean_unsigned_to_nat(4u);
v___x_951_ = lean_nat_mul(v_size_x27_947_, v___x_950_);
v___x_952_ = lean_unsigned_to_nat(3u);
v___x_953_ = lean_nat_div(v___x_951_, v___x_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_array_get_size(v_buckets_x27_949_);
v___x_955_ = lean_nat_dec_le(v___x_953_, v___x_954_);
lean_dec(v___x_953_);
if (v___x_955_ == 0)
{
lean_object* v_val_956_; lean_object* v___x_958_; 
v_val_956_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_949_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v_val_956_);
lean_ctor_set(v___x_929_, 0, v_size_x27_947_);
v___x_958_ = v___x_929_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_size_x27_947_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_val_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_961_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v_buckets_x27_949_);
lean_ctor_set(v___x_929_, 0, v_size_x27_947_);
v___x_961_ = v___x_929_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_size_x27_947_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_buckets_x27_949_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v___x_963_; lean_object* v_buckets_x27_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_inc(v_bkt_944_);
v___x_963_ = lean_box(0);
v_buckets_x27_964_ = lean_array_uset(v_buckets_927_, v___x_943_, v___x_963_);
v___x_965_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_924_, v_b_925_, v_bkt_944_);
v___x_966_ = lean_array_uset(v_buckets_x27_964_, v___x_943_, v___x_965_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_966_);
v___x_968_ = v___x_929_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_size_926_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_971_, lean_object* v_a_972_){
_start:
{
switch(lean_obj_tag(v_x_971_))
{
case 0:
{
lean_object* v_x_973_; lean_object* v_ty_974_; lean_object* v_b_975_; lean_object* v___x_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_x_973_ = lean_ctor_get(v_x_971_, 0);
lean_inc(v_x_973_);
v_ty_974_ = lean_ctor_get(v_x_971_, 1);
lean_inc(v_ty_974_);
v_b_975_ = lean_ctor_get(v_x_971_, 3);
lean_inc(v_b_975_);
lean_dec_ref(v_x_971_);
v___x_976_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_975_, v_a_972_);
v_fst_977_ = lean_ctor_get(v___x_976_, 0);
v_snd_978_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v___x_976_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v___x_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_977_, v_x_973_, v_ty_974_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_978_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
case 1:
{
lean_object* v_j_987_; lean_object* v_xs_988_; lean_object* v_v_989_; lean_object* v_b_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v_j_987_ = lean_ctor_get(v_x_971_, 0);
lean_inc(v_j_987_);
v_xs_988_ = lean_ctor_get(v_x_971_, 1);
lean_inc_ref(v_xs_988_);
v_v_989_ = lean_ctor_get(v_x_971_, 2);
lean_inc(v_v_989_);
v_b_990_ = lean_ctor_get(v_x_971_, 3);
lean_inc(v_b_990_);
lean_dec_ref(v_x_971_);
v___x_991_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_990_, v_a_972_);
v___x_992_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_989_, v___x_991_);
v___x_993_ = l_Lean_IR_CollectMaps_collectParams(v_xs_988_, v___x_992_);
v_fst_994_ = lean_ctor_get(v___x_993_, 0);
v_snd_995_ = lean_ctor_get(v___x_993_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v___x_993_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snd_995_);
lean_inc(v_fst_994_);
lean_dec(v___x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_995_, v_j_987_, v_xs_988_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
case 9:
{
lean_object* v_cs_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_cs_1004_ = lean_ctor_get(v_x_971_, 3);
lean_inc_ref(v_cs_1004_);
lean_dec_ref(v_x_971_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_array_get_size(v_cs_1004_);
v___x_1007_ = lean_nat_dec_lt(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec_ref(v_cs_1004_);
return v_a_972_;
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_le(v___x_1006_, v___x_1006_);
if (v___x_1008_ == 0)
{
if (v___x_1007_ == 0)
{
lean_dec_ref(v_cs_1004_);
return v_a_972_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = lean_usize_of_nat(v___x_1006_);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1004_, v___x_1009_, v___x_1010_, v_a_972_);
lean_dec_ref(v_cs_1004_);
return v___x_1011_;
}
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = lean_usize_of_nat(v___x_1006_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1004_, v___x_1012_, v___x_1013_, v_a_972_);
lean_dec_ref(v_cs_1004_);
return v___x_1014_;
}
}
}
default: 
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Lean_IR_FnBody_isTerminal(v_x_971_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_IR_FnBody_body(v_x_971_);
lean_dec(v_x_971_);
v_x_971_ = v___x_1016_;
goto _start;
}
else
{
lean_dec(v_x_971_);
return v_a_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_1018_, size_t v_i_1019_, size_t v_stop_1020_, lean_object* v_b_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_eq(v_i_1019_, v_stop_1020_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; 
v___x_1023_ = lean_array_uget_borrowed(v_as_1018_, v_i_1019_);
v___x_1024_ = l_Lean_IR_Alt_body(v___x_1023_);
v___x_1025_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1024_, v_b_1021_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1019_, v___x_1026_);
v_i_1019_ = v___x_1027_;
v_b_1021_ = v___x_1025_;
goto _start;
}
else
{
return v_b_1021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1029_, lean_object* v_i_1030_, lean_object* v_stop_1031_, lean_object* v_b_1032_){
_start:
{
size_t v_i_boxed_1033_; size_t v_stop_boxed_1034_; lean_object* v_res_1035_; 
v_i_boxed_1033_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_stop_boxed_1034_ = lean_unbox_usize(v_stop_1031_);
lean_dec(v_stop_1031_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1029_, v_i_boxed_1033_, v_stop_boxed_1034_, v_b_1032_);
lean_dec_ref(v_as_1029_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1036_, lean_object* v_m_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1037_, v_a_1038_, v_b_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1041_, lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1042_, v_x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1045_, lean_object* v_a_1046_, lean_object* v_x_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1045_, v_a_1046_, v_x_1047_);
lean_dec(v_x_1047_);
lean_dec(v_a_1046_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1050_, lean_object* v_data_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1053_, lean_object* v_a_1054_, lean_object* v_b_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1054_, v_b_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1058_, lean_object* v_i_1059_, lean_object* v_source_1060_, lean_object* v_target_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1059_, v_source_1060_, v_target_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1064_, v_x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1067_, lean_object* v_a_1068_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v_xs_1069_; lean_object* v_body_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_xs_1069_ = lean_ctor_get(v_x_1067_, 1);
lean_inc_ref(v_xs_1069_);
v_body_1070_ = lean_ctor_get(v_x_1067_, 3);
lean_inc(v_body_1070_);
lean_dec_ref(v_x_1067_);
v___x_1071_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1070_, v_a_1068_);
v___x_1072_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1069_, v___x_1071_);
lean_dec_ref(v_xs_1069_);
return v___x_1072_;
}
else
{
lean_dec_ref(v_x_1067_);
return v_a_1068_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_unsigned_to_nat(16u);
v___x_1075_ = lean_mk_array(v___x_1074_, v___x_1073_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1076_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1083_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1081_, v___x_1082_);
return v___x_1083_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_EmitUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_EmitUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_EmitUtil(builtin);
}
#ifdef __cplusplus
}
#endif
