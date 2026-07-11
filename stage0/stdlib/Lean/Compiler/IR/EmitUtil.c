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
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_instBEqJoinPointId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_instBEqVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_instHashableVarId_hash___boxed(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_IR_collectUsedDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_IR_collectUsedDecls___closed__0 = (const lean_object*)&l_Lean_IR_collectUsedDecls___closed__0_value;
static lean_once_cell_t l_Lean_IR_collectUsedDecls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_collectUsedDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object*, lean_object*);
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
lean_object* v___x_24_; lean_object* v_toImport_25_; uint8_t v_irPhases_26_; uint8_t v___x_27_; uint8_t v___y_29_; uint8_t v___x_33_; uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_24_ = lean_array_uget_borrowed(v_as_20_, v_i_21_);
v_toImport_25_ = lean_ctor_get(v___x_24_, 0);
v_irPhases_26_ = lean_ctor_get_uint8(v___x_24_, sizeof(void*)*1);
v___x_27_ = 1;
v___x_33_ = 1;
v___x_34_ = l_Lean_instBEqIRPhases_beq(v_irPhases_26_, v___x_33_);
v___x_35_ = lean_bool_not(v___x_34_);
if (v___x_35_ == 0)
{
v___y_29_ = v___x_35_;
goto v___jp_28_;
}
else
{
lean_object* v_module_36_; uint8_t v___x_37_; 
v_module_36_ = lean_ctor_get(v_toImport_25_, 0);
v___x_37_ = l_Lean_Name_isPrefixOf(v_modulePrefix_19_, v_module_36_);
v___y_29_ = v___x_37_;
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
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_39_, lean_object* v_as_40_, lean_object* v_i_41_, lean_object* v_stop_42_){
_start:
{
size_t v_i_boxed_43_; size_t v_stop_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_i_boxed_43_ = lean_unbox_usize(v_i_41_);
lean_dec(v_i_41_);
v_stop_boxed_44_ = lean_unbox_usize(v_stop_42_);
lean_dec(v_stop_42_);
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_39_, v_as_40_, v_i_boxed_43_, v_stop_boxed_44_);
lean_dec_ref(v_as_40_);
lean_dec(v_modulePrefix_39_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_usesModuleFrom(lean_object* v_env_47_, lean_object* v_modulePrefix_48_){
_start:
{
lean_object* v___x_49_; lean_object* v_modules_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_49_ = l_Lean_Environment_header(v_env_47_);
v_modules_50_ = lean_ctor_get(v___x_49_, 3);
lean_inc_ref(v_modules_50_);
lean_dec_ref(v___x_49_);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_array_get_size(v_modules_50_);
v___x_53_ = lean_nat_dec_lt(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_dec_ref(v_modules_50_);
return v___x_53_;
}
else
{
if (v___x_53_ == 0)
{
lean_dec_ref(v_modules_50_);
return v___x_53_;
}
else
{
size_t v___x_54_; size_t v___x_55_; uint8_t v___x_56_; 
v___x_54_ = ((size_t)0ULL);
v___x_55_ = lean_usize_of_nat(v___x_52_);
v___x_56_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_48_, v_modules_50_, v___x_54_, v___x_55_);
lean_dec_ref(v_modules_50_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_usesModuleFrom___boxed(lean_object* v_env_57_, lean_object* v_modulePrefix_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_IR_usesModuleFrom(v_env_57_, v_modulePrefix_58_);
lean_dec(v_modulePrefix_58_);
lean_dec_ref(v_env_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___redArg(lean_object* v_f_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_set_64_; lean_object* v_order_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_89_; 
v_set_64_ = lean_ctor_get(v_a_63_, 0);
v_order_65_ = lean_ctor_get(v_a_63_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_a_63_);
if (v_isSharedCheck_89_ == 0)
{
v___x_67_ = v_a_63_;
v_isShared_68_ = v_isSharedCheck_89_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_order_65_);
lean_inc(v_set_64_);
lean_dec(v_a_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_89_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v_fst_71_; lean_object* v_snd_72_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_69_ = lean_box(0);
v___x_84_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_64_);
lean_inc(v_f_62_);
v___x_85_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_84_, v_f_62_, v_set_64_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_inc(v_f_62_);
v___x_86_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_84_, v_f_62_, v___x_69_, v_set_64_);
v___x_87_ = lean_box(v___x_85_);
v_fst_71_ = v___x_87_;
v_snd_72_ = v___x_86_;
goto v___jp_70_;
}
else
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(v___x_85_);
v_fst_71_ = v___x_88_;
v_snd_72_ = v_set_64_;
goto v___jp_70_;
}
v___jp_70_:
{
uint8_t v___x_73_; uint8_t v___x_74_; 
v___x_73_ = lean_unbox(v_fst_71_);
lean_dec(v_fst_71_);
v___x_74_ = lean_bool_not(v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_76_; 
lean_dec(v_f_62_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v_snd_72_);
v___x_76_ = v___x_67_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_snd_72_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_order_65_);
v___x_76_ = v_reuseFailAlloc_78_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_69_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
return v___x_77_;
}
}
else
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_array_push(v_order_65_, v_f_62_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_79_);
lean_ctor_set(v___x_67_, 0, v_snd_72_);
v___x_81_ = v___x_67_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_snd_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_79_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_69_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
return v___x_82_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* v_f_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_set_93_; lean_object* v_order_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_118_; 
v_set_93_ = lean_ctor_get(v_a_92_, 0);
v_order_94_ = lean_ctor_get(v_a_92_, 1);
v_isSharedCheck_118_ = !lean_is_exclusive(v_a_92_);
if (v_isSharedCheck_118_ == 0)
{
v___x_96_ = v_a_92_;
v_isShared_97_ = v_isSharedCheck_118_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_order_94_);
lean_inc(v_set_93_);
lean_dec(v_a_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_118_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v_fst_100_; lean_object* v_snd_101_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_98_ = lean_box(0);
v___x_113_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_93_);
lean_inc(v_f_90_);
v___x_114_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_113_, v_f_90_, v_set_93_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_inc(v_f_90_);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_113_, v_f_90_, v___x_98_, v_set_93_);
v___x_116_ = lean_box(v___x_114_);
v_fst_100_ = v___x_116_;
v_snd_101_ = v___x_115_;
goto v___jp_99_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(v___x_114_);
v_fst_100_ = v___x_117_;
v_snd_101_ = v_set_93_;
goto v___jp_99_;
}
v___jp_99_:
{
uint8_t v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unbox(v_fst_100_);
lean_dec(v_fst_100_);
v___x_103_ = lean_bool_not(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_105_; 
lean_dec(v_f_90_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v_snd_101_);
v___x_105_ = v___x_96_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_snd_101_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_order_94_);
v___x_105_ = v_reuseFailAlloc_107_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_98_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
return v___x_106_;
}
}
else
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = lean_array_push(v_order_94_, v_f_90_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_108_);
lean_ctor_set(v___x_96_, 0, v_snd_101_);
v___x_110_ = v___x_96_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_snd_101_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_112_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_98_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* v_f_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_IR_CollectUsedDecls_collect(v_f_119_, v_a_120_, v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object* v_k_123_, lean_object* v_v_124_, lean_object* v_t_125_){
_start:
{
if (lean_obj_tag(v_t_125_) == 0)
{
lean_object* v_size_126_; lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v_l_129_; lean_object* v_r_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_410_; 
v_size_126_ = lean_ctor_get(v_t_125_, 0);
v_k_127_ = lean_ctor_get(v_t_125_, 1);
v_v_128_ = lean_ctor_get(v_t_125_, 2);
v_l_129_ = lean_ctor_get(v_t_125_, 3);
v_r_130_ = lean_ctor_get(v_t_125_, 4);
v_isSharedCheck_410_ = !lean_is_exclusive(v_t_125_);
if (v_isSharedCheck_410_ == 0)
{
v___x_132_ = v_t_125_;
v_isShared_133_ = v_isSharedCheck_410_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_r_130_);
lean_inc(v_l_129_);
lean_inc(v_v_128_);
lean_inc(v_k_127_);
lean_inc(v_size_126_);
lean_dec(v_t_125_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_410_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v___x_134_; 
v___x_134_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_123_, v_k_127_);
switch(v___x_134_)
{
case 0:
{
lean_object* v_impl_135_; lean_object* v___x_136_; 
lean_dec(v_size_126_);
v_impl_135_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_123_, v_v_124_, v_l_129_);
v___x_136_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_130_) == 0)
{
lean_object* v_size_137_; lean_object* v_size_138_; lean_object* v_k_139_; lean_object* v_v_140_; lean_object* v_l_141_; lean_object* v_r_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_size_137_ = lean_ctor_get(v_r_130_, 0);
v_size_138_ = lean_ctor_get(v_impl_135_, 0);
lean_inc(v_size_138_);
v_k_139_ = lean_ctor_get(v_impl_135_, 1);
lean_inc(v_k_139_);
v_v_140_ = lean_ctor_get(v_impl_135_, 2);
lean_inc(v_v_140_);
v_l_141_ = lean_ctor_get(v_impl_135_, 3);
lean_inc(v_l_141_);
v_r_142_ = lean_ctor_get(v_impl_135_, 4);
lean_inc(v_r_142_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_mul(v___x_143_, v_size_137_);
v___x_145_ = lean_nat_dec_lt(v___x_144_, v_size_138_);
lean_dec(v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v_r_142_);
lean_dec(v_l_141_);
lean_dec(v_v_140_);
lean_dec(v_k_139_);
v___x_146_ = lean_nat_add(v___x_136_, v_size_138_);
lean_dec(v_size_138_);
v___x_147_ = lean_nat_add(v___x_146_, v_size_137_);
lean_dec(v___x_146_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 3, v_impl_135_);
lean_ctor_set(v___x_132_, 0, v___x_147_);
v___x_149_ = v___x_132_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_impl_135_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_r_130_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_216_; 
v_isSharedCheck_216_ = !lean_is_exclusive(v_impl_135_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; lean_object* v_unused_220_; lean_object* v_unused_221_; 
v_unused_217_ = lean_ctor_get(v_impl_135_, 4);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_impl_135_, 3);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_impl_135_, 2);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_impl_135_, 1);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_impl_135_, 0);
lean_dec(v_unused_221_);
v___x_152_ = v_impl_135_;
v_isShared_153_ = v_isSharedCheck_216_;
goto v_resetjp_151_;
}
else
{
lean_dec(v_impl_135_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_216_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_size_154_; lean_object* v_size_155_; lean_object* v_k_156_; lean_object* v_v_157_; lean_object* v_l_158_; lean_object* v_r_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_size_154_ = lean_ctor_get(v_l_141_, 0);
v_size_155_ = lean_ctor_get(v_r_142_, 0);
v_k_156_ = lean_ctor_get(v_r_142_, 1);
v_v_157_ = lean_ctor_get(v_r_142_, 2);
v_l_158_ = lean_ctor_get(v_r_142_, 3);
v_r_159_ = lean_ctor_get(v_r_142_, 4);
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_nat_mul(v___x_160_, v_size_154_);
v___x_162_ = lean_nat_dec_lt(v_size_155_, v___x_161_);
lean_dec(v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_191_; 
lean_inc(v_r_159_);
lean_inc(v_l_158_);
lean_inc(v_v_157_);
lean_inc(v_k_156_);
v_isSharedCheck_191_ = !lean_is_exclusive(v_r_142_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; lean_object* v_unused_196_; 
v_unused_192_ = lean_ctor_get(v_r_142_, 4);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_r_142_, 3);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_r_142_, 2);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_r_142_, 1);
lean_dec(v_unused_195_);
v_unused_196_ = lean_ctor_get(v_r_142_, 0);
lean_dec(v_unused_196_);
v___x_164_ = v_r_142_;
v_isShared_165_ = v_isSharedCheck_191_;
goto v_resetjp_163_;
}
else
{
lean_dec(v_r_142_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_191_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___x_179_; lean_object* v___y_181_; 
v___x_166_ = lean_nat_add(v___x_136_, v_size_138_);
lean_dec(v_size_138_);
v___x_167_ = lean_nat_add(v___x_166_, v_size_137_);
lean_dec(v___x_166_);
v___x_179_ = lean_nat_add(v___x_136_, v_size_154_);
if (lean_obj_tag(v_l_158_) == 0)
{
lean_object* v_size_189_; 
v_size_189_ = lean_ctor_get(v_l_158_, 0);
lean_inc(v_size_189_);
v___y_181_ = v_size_189_;
goto v___jp_180_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___y_181_ = v___x_190_;
goto v___jp_180_;
}
v___jp_168_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_nat_add(v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec(v___y_170_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v_r_130_);
lean_ctor_set(v___x_164_, 3, v_r_159_);
lean_ctor_set(v___x_164_, 2, v_v_128_);
lean_ctor_set(v___x_164_, 1, v_k_127_);
lean_ctor_set(v___x_164_, 0, v___x_172_);
v___x_174_ = v___x_164_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_r_159_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_r_130_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v___x_174_);
lean_ctor_set(v___x_152_, 3, v___y_169_);
lean_ctor_set(v___x_152_, 2, v_v_157_);
lean_ctor_set(v___x_152_, 1, v_k_156_);
lean_ctor_set(v___x_152_, 0, v___x_167_);
v___x_176_ = v___x_152_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_156_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_157_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v___y_169_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = lean_nat_add(v___x_179_, v___y_181_);
lean_dec(v___y_181_);
lean_dec(v___x_179_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_l_158_);
lean_ctor_set(v___x_132_, 3, v_l_141_);
lean_ctor_set(v___x_132_, 2, v_v_140_);
lean_ctor_set(v___x_132_, 1, v_k_139_);
lean_ctor_set(v___x_132_, 0, v___x_182_);
v___x_184_ = v___x_132_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_k_139_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_v_140_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_l_141_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v_l_158_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_nat_add(v___x_136_, v_size_137_);
if (lean_obj_tag(v_r_159_) == 0)
{
lean_object* v_size_186_; 
v_size_186_ = lean_ctor_get(v_r_159_, 0);
lean_inc(v_size_186_);
v___y_169_ = v___x_184_;
v___y_170_ = v___x_185_;
v___y_171_ = v_size_186_;
goto v___jp_168_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___y_169_ = v___x_184_;
v___y_170_ = v___x_185_;
v___y_171_ = v___x_187_;
goto v___jp_168_;
}
}
}
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
lean_del_object(v___x_132_);
v___x_197_ = lean_nat_add(v___x_136_, v_size_138_);
lean_dec(v_size_138_);
v___x_198_ = lean_nat_add(v___x_197_, v_size_137_);
lean_dec(v___x_197_);
v___x_199_ = lean_nat_add(v___x_136_, v_size_137_);
v___x_200_ = lean_nat_add(v___x_199_, v_size_155_);
lean_dec(v___x_199_);
lean_inc_ref(v_r_130_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 4, v_r_130_);
lean_ctor_set(v___x_152_, 3, v_r_142_);
lean_ctor_set(v___x_152_, 2, v_v_128_);
lean_ctor_set(v___x_152_, 1, v_k_127_);
lean_ctor_set(v___x_152_, 0, v___x_200_);
v___x_202_ = v___x_152_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_r_142_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_r_130_);
v___x_202_ = v_reuseFailAlloc_215_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_isSharedCheck_209_ = !lean_is_exclusive(v_r_130_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; 
v_unused_210_ = lean_ctor_get(v_r_130_, 4);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_r_130_, 3);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_r_130_, 2);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_r_130_, 1);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_r_130_, 0);
lean_dec(v_unused_214_);
v___x_204_ = v_r_130_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_dec(v_r_130_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 4, v___x_202_);
lean_ctor_set(v___x_204_, 3, v_l_141_);
lean_ctor_set(v___x_204_, 2, v_v_140_);
lean_ctor_set(v___x_204_, 1, v_k_139_);
lean_ctor_set(v___x_204_, 0, v___x_198_);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_k_139_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_140_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_l_141_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v___x_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_222_; 
v_l_222_ = lean_ctor_get(v_impl_135_, 3);
lean_inc(v_l_222_);
if (lean_obj_tag(v_l_222_) == 0)
{
lean_object* v_r_223_; lean_object* v_k_224_; lean_object* v_v_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_236_; 
v_r_223_ = lean_ctor_get(v_impl_135_, 4);
v_k_224_ = lean_ctor_get(v_impl_135_, 1);
v_v_225_ = lean_ctor_get(v_impl_135_, 2);
v_isSharedCheck_236_ = !lean_is_exclusive(v_impl_135_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_237_ = lean_ctor_get(v_impl_135_, 3);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_impl_135_, 0);
lean_dec(v_unused_238_);
v___x_227_ = v_impl_135_;
v_isShared_228_ = v_isSharedCheck_236_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_r_223_);
lean_inc(v_v_225_);
lean_inc(v_k_224_);
lean_dec(v_impl_135_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_236_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_223_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 3, v_r_223_);
lean_ctor_set(v___x_227_, 2, v_v_128_);
lean_ctor_set(v___x_227_, 1, v_k_127_);
lean_ctor_set(v___x_227_, 0, v___x_136_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_r_223_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_r_223_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_231_);
lean_ctor_set(v___x_132_, 3, v_l_222_);
lean_ctor_set(v___x_132_, 2, v_v_225_);
lean_ctor_set(v___x_132_, 1, v_k_224_);
lean_ctor_set(v___x_132_, 0, v___x_229_);
v___x_233_ = v___x_132_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_225_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_l_222_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_r_239_; 
v_r_239_ = lean_ctor_get(v_impl_135_, 4);
lean_inc(v_r_239_);
if (lean_obj_tag(v_r_239_) == 0)
{
lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_264_; 
v_k_240_ = lean_ctor_get(v_impl_135_, 1);
v_v_241_ = lean_ctor_get(v_impl_135_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_impl_135_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; 
v_unused_265_ = lean_ctor_get(v_impl_135_, 4);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_impl_135_, 3);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_impl_135_, 0);
lean_dec(v_unused_267_);
v___x_243_ = v_impl_135_;
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_v_241_);
lean_inc(v_k_240_);
lean_dec(v_impl_135_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_264_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_k_245_; lean_object* v_v_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_260_; 
v_k_245_ = lean_ctor_get(v_r_239_, 1);
v_v_246_ = lean_ctor_get(v_r_239_, 2);
v_isSharedCheck_260_ = !lean_is_exclusive(v_r_239_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_261_ = lean_ctor_get(v_r_239_, 4);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_r_239_, 3);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_r_239_, 0);
lean_dec(v_unused_263_);
v___x_248_ = v_r_239_;
v_isShared_249_ = v_isSharedCheck_260_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_v_246_);
lean_inc(v_k_245_);
lean_dec(v_r_239_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_260_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(3u);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v_l_222_);
lean_ctor_set(v___x_248_, 3, v_l_222_);
lean_ctor_set(v___x_248_, 2, v_v_241_);
lean_ctor_set(v___x_248_, 1, v_k_240_);
lean_ctor_set(v___x_248_, 0, v___x_136_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_l_222_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_l_222_);
v___x_252_ = v_reuseFailAlloc_259_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 4, v_l_222_);
lean_ctor_set(v___x_243_, 2, v_v_128_);
lean_ctor_set(v___x_243_, 1, v_k_127_);
lean_ctor_set(v___x_243_, 0, v___x_136_);
v___x_254_ = v___x_243_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_l_222_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_l_222_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_254_);
lean_ctor_set(v___x_132_, 3, v___x_252_);
lean_ctor_set(v___x_132_, 2, v_v_246_);
lean_ctor_set(v___x_132_, 1, v_k_245_);
lean_ctor_set(v___x_132_, 0, v___x_250_);
v___x_256_ = v___x_132_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_245_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_v_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(2u);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_r_239_);
lean_ctor_set(v___x_132_, 3, v_impl_135_);
lean_ctor_set(v___x_132_, 0, v___x_268_);
v___x_270_ = v___x_132_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_impl_135_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_r_239_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
case 1:
{
lean_object* v___x_273_; 
lean_dec(v_v_128_);
lean_dec(v_k_127_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 2, v_v_124_);
lean_ctor_set(v___x_132_, 1, v_k_123_);
v___x_273_ = v___x_132_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_size_126_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_k_123_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_v_124_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_r_130_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
default: 
{
lean_object* v_impl_275_; lean_object* v___x_276_; 
lean_dec(v_size_126_);
v_impl_275_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_123_, v_v_124_, v_r_130_);
v___x_276_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_129_) == 0)
{
lean_object* v_size_277_; lean_object* v_size_278_; lean_object* v_k_279_; lean_object* v_v_280_; lean_object* v_l_281_; lean_object* v_r_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_size_277_ = lean_ctor_get(v_l_129_, 0);
v_size_278_ = lean_ctor_get(v_impl_275_, 0);
lean_inc(v_size_278_);
v_k_279_ = lean_ctor_get(v_impl_275_, 1);
lean_inc(v_k_279_);
v_v_280_ = lean_ctor_get(v_impl_275_, 2);
lean_inc(v_v_280_);
v_l_281_ = lean_ctor_get(v_impl_275_, 3);
lean_inc(v_l_281_);
v_r_282_ = lean_ctor_get(v_impl_275_, 4);
lean_inc(v_r_282_);
v___x_283_ = lean_unsigned_to_nat(3u);
v___x_284_ = lean_nat_mul(v___x_283_, v_size_277_);
v___x_285_ = lean_nat_dec_lt(v___x_284_, v_size_278_);
lean_dec(v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec(v_r_282_);
lean_dec(v_l_281_);
lean_dec(v_v_280_);
lean_dec(v_k_279_);
v___x_286_ = lean_nat_add(v___x_276_, v_size_277_);
v___x_287_ = lean_nat_add(v___x_286_, v_size_278_);
lean_dec(v_size_278_);
lean_dec(v___x_286_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_impl_275_);
lean_ctor_set(v___x_132_, 0, v___x_287_);
v___x_289_ = v___x_132_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v_impl_275_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_354_; 
v_isSharedCheck_354_ = !lean_is_exclusive(v_impl_275_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_355_ = lean_ctor_get(v_impl_275_, 4);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_275_, 3);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_impl_275_, 2);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_impl_275_, 1);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_impl_275_, 0);
lean_dec(v_unused_359_);
v___x_292_ = v_impl_275_;
v_isShared_293_ = v_isSharedCheck_354_;
goto v_resetjp_291_;
}
else
{
lean_dec(v_impl_275_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_354_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_size_294_; lean_object* v_k_295_; lean_object* v_v_296_; lean_object* v_l_297_; lean_object* v_r_298_; lean_object* v_size_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_size_294_ = lean_ctor_get(v_l_281_, 0);
v_k_295_ = lean_ctor_get(v_l_281_, 1);
v_v_296_ = lean_ctor_get(v_l_281_, 2);
v_l_297_ = lean_ctor_get(v_l_281_, 3);
v_r_298_ = lean_ctor_get(v_l_281_, 4);
v_size_299_ = lean_ctor_get(v_r_282_, 0);
v___x_300_ = lean_unsigned_to_nat(2u);
v___x_301_ = lean_nat_mul(v___x_300_, v_size_299_);
v___x_302_ = lean_nat_dec_lt(v_size_294_, v___x_301_);
lean_dec(v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_330_; 
lean_inc(v_r_298_);
lean_inc(v_l_297_);
lean_inc(v_v_296_);
lean_inc(v_k_295_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_l_281_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_331_ = lean_ctor_get(v_l_281_, 4);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_l_281_, 3);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_l_281_, 2);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_l_281_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_l_281_, 0);
lean_dec(v_unused_335_);
v___x_304_ = v_l_281_;
v_isShared_305_ = v_isSharedCheck_330_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_l_281_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_330_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_320_; 
v___x_306_ = lean_nat_add(v___x_276_, v_size_277_);
v___x_307_ = lean_nat_add(v___x_306_, v_size_278_);
lean_dec(v_size_278_);
if (lean_obj_tag(v_l_297_) == 0)
{
lean_object* v_size_328_; 
v_size_328_ = lean_ctor_get(v_l_297_, 0);
lean_inc(v_size_328_);
v___y_320_ = v_size_328_;
goto v___jp_319_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___y_320_ = v___x_329_;
goto v___jp_319_;
}
v___jp_308_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_nat_add(v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec(v___y_310_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v_r_282_);
lean_ctor_set(v___x_304_, 3, v_r_298_);
lean_ctor_set(v___x_304_, 2, v_v_280_);
lean_ctor_set(v___x_304_, 1, v_k_279_);
lean_ctor_set(v___x_304_, 0, v___x_312_);
v___x_314_ = v___x_304_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_k_279_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_v_280_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_r_298_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v_r_282_);
v___x_314_ = v_reuseFailAlloc_318_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 4, v___x_314_);
lean_ctor_set(v___x_292_, 3, v___y_309_);
lean_ctor_set(v___x_292_, 2, v_v_296_);
lean_ctor_set(v___x_292_, 1, v_k_295_);
lean_ctor_set(v___x_292_, 0, v___x_307_);
v___x_316_ = v___x_292_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_295_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_296_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v___y_309_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_nat_add(v___x_306_, v___y_320_);
lean_dec(v___y_320_);
lean_dec(v___x_306_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_l_297_);
lean_ctor_set(v___x_132_, 0, v___x_321_);
v___x_323_ = v___x_132_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_l_297_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; 
v___x_324_ = lean_nat_add(v___x_276_, v_size_299_);
if (lean_obj_tag(v_r_298_) == 0)
{
lean_object* v_size_325_; 
v_size_325_ = lean_ctor_get(v_r_298_, 0);
lean_inc(v_size_325_);
v___y_309_ = v___x_323_;
v___y_310_ = v___x_324_;
v___y_311_ = v_size_325_;
goto v___jp_308_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___y_309_ = v___x_323_;
v___y_310_ = v___x_324_;
v___y_311_ = v___x_326_;
goto v___jp_308_;
}
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_del_object(v___x_132_);
v___x_336_ = lean_nat_add(v___x_276_, v_size_277_);
v___x_337_ = lean_nat_add(v___x_336_, v_size_278_);
lean_dec(v_size_278_);
v___x_338_ = lean_nat_add(v___x_336_, v_size_294_);
lean_dec(v___x_336_);
lean_inc_ref(v_l_129_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 4, v_l_281_);
lean_ctor_set(v___x_292_, 3, v_l_129_);
lean_ctor_set(v___x_292_, 2, v_v_128_);
lean_ctor_set(v___x_292_, 1, v_k_127_);
lean_ctor_set(v___x_292_, 0, v___x_338_);
v___x_340_ = v___x_292_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_l_129_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_l_281_);
v___x_340_ = v_reuseFailAlloc_353_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_isSharedCheck_347_ = !lean_is_exclusive(v_l_129_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_348_ = lean_ctor_get(v_l_129_, 4);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_l_129_, 3);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_l_129_, 2);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_l_129_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_l_129_, 0);
lean_dec(v_unused_352_);
v___x_342_ = v_l_129_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_l_129_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_r_282_);
lean_ctor_set(v___x_342_, 3, v___x_340_);
lean_ctor_set(v___x_342_, 2, v_v_280_);
lean_ctor_set(v___x_342_, 1, v_k_279_);
lean_ctor_set(v___x_342_, 0, v___x_337_);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_279_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_280_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_r_282_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_360_; 
v_l_360_ = lean_ctor_get(v_impl_275_, 3);
lean_inc(v_l_360_);
if (lean_obj_tag(v_l_360_) == 0)
{
lean_object* v_r_361_; lean_object* v_k_362_; lean_object* v_v_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_386_; 
v_r_361_ = lean_ctor_get(v_impl_275_, 4);
v_k_362_ = lean_ctor_get(v_impl_275_, 1);
v_v_363_ = lean_ctor_get(v_impl_275_, 2);
v_isSharedCheck_386_ = !lean_is_exclusive(v_impl_275_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; lean_object* v_unused_388_; 
v_unused_387_ = lean_ctor_get(v_impl_275_, 3);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_impl_275_, 0);
lean_dec(v_unused_388_);
v___x_365_ = v_impl_275_;
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_r_361_);
lean_inc(v_v_363_);
lean_inc(v_k_362_);
lean_dec(v_impl_275_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_386_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_k_367_; lean_object* v_v_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_382_; 
v_k_367_ = lean_ctor_get(v_l_360_, 1);
v_v_368_ = lean_ctor_get(v_l_360_, 2);
v_isSharedCheck_382_ = !lean_is_exclusive(v_l_360_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; lean_object* v_unused_384_; lean_object* v_unused_385_; 
v_unused_383_ = lean_ctor_get(v_l_360_, 4);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_l_360_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_l_360_, 0);
lean_dec(v_unused_385_);
v___x_370_ = v_l_360_;
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_v_368_);
lean_inc(v_k_367_);
lean_dec(v_l_360_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_382_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_361_, 2);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 4, v_r_361_);
lean_ctor_set(v___x_370_, 3, v_r_361_);
lean_ctor_set(v___x_370_, 2, v_v_128_);
lean_ctor_set(v___x_370_, 1, v_k_127_);
lean_ctor_set(v___x_370_, 0, v___x_276_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_r_361_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_r_361_);
v___x_374_ = v_reuseFailAlloc_381_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
lean_inc(v_r_361_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 3, v_r_361_);
lean_ctor_set(v___x_365_, 0, v___x_276_);
v___x_376_ = v___x_365_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_r_361_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_r_361_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v___x_376_);
lean_ctor_set(v___x_132_, 3, v___x_374_);
lean_ctor_set(v___x_132_, 2, v_v_368_);
lean_ctor_set(v___x_132_, 1, v_k_367_);
lean_ctor_set(v___x_132_, 0, v___x_372_);
v___x_378_ = v___x_132_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_k_367_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_v_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
else
{
lean_object* v_r_389_; 
v_r_389_ = lean_ctor_get(v_impl_275_, 4);
lean_inc(v_r_389_);
if (lean_obj_tag(v_r_389_) == 0)
{
lean_object* v_k_390_; lean_object* v_v_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_402_; 
v_k_390_ = lean_ctor_get(v_impl_275_, 1);
v_v_391_ = lean_ctor_get(v_impl_275_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_impl_275_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; 
v_unused_403_ = lean_ctor_get(v_impl_275_, 4);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_impl_275_, 3);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_impl_275_, 0);
lean_dec(v_unused_405_);
v___x_393_ = v_impl_275_;
v_isShared_394_ = v_isSharedCheck_402_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_v_391_);
lean_inc(v_k_390_);
lean_dec(v_impl_275_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_402_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_unsigned_to_nat(3u);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 4, v_l_360_);
lean_ctor_set(v___x_393_, 2, v_v_128_);
lean_ctor_set(v___x_393_, 1, v_k_127_);
lean_ctor_set(v___x_393_, 0, v___x_276_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v_l_360_);
v___x_397_ = v_reuseFailAlloc_401_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_r_389_);
lean_ctor_set(v___x_132_, 3, v___x_397_);
lean_ctor_set(v___x_132_, 2, v_v_391_);
lean_ctor_set(v___x_132_, 1, v_k_390_);
lean_ctor_set(v___x_132_, 0, v___x_395_);
v___x_399_ = v___x_132_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_390_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_391_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_r_389_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(2u);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_impl_275_);
lean_ctor_set(v___x_132_, 3, v_r_389_);
lean_ctor_set(v___x_132_, 0, v___x_406_);
v___x_408_ = v___x_132_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_r_389_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_impl_275_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
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
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_k_123_);
lean_ctor_set(v___x_412_, 2, v_v_124_);
lean_ctor_set(v___x_412_, 3, v_t_125_);
lean_ctor_set(v___x_412_, 4, v_t_125_);
return v___x_412_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object* v_k_413_, lean_object* v_t_414_){
_start:
{
if (lean_obj_tag(v_t_414_) == 0)
{
lean_object* v_k_415_; lean_object* v_l_416_; lean_object* v_r_417_; uint8_t v___x_418_; 
v_k_415_ = lean_ctor_get(v_t_414_, 1);
v_l_416_ = lean_ctor_get(v_t_414_, 3);
v_r_417_ = lean_ctor_get(v_t_414_, 4);
v___x_418_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_413_, v_k_415_);
switch(v___x_418_)
{
case 0:
{
v_t_414_ = v_l_416_;
goto _start;
}
case 1:
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
default: 
{
v_t_414_ = v_r_417_;
goto _start;
}
}
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object* v_k_423_, lean_object* v_t_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_423_, v_t_424_);
lean_dec(v_t_424_);
lean_dec(v_k_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* v_x_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
switch(lean_obj_tag(v_x_427_))
{
case 0:
{
lean_object* v_e_430_; lean_object* v_b_431_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v_f_446_; lean_object* v___y_447_; lean_object* v___y_448_; 
v_e_430_ = lean_ctor_get(v_x_427_, 2);
lean_inc_ref(v_e_430_);
v_b_431_ = lean_ctor_get(v_x_427_, 3);
lean_inc(v_b_431_);
lean_dec_ref_known(v_x_427_, 4);
switch(lean_obj_tag(v_e_430_))
{
case 6:
{
lean_object* v_c_456_; 
v_c_456_ = lean_ctor_get(v_e_430_, 0);
lean_inc(v_c_456_);
lean_dec_ref_known(v_e_430_, 2);
v_f_446_ = v_c_456_;
v___y_447_ = v_a_428_;
v___y_448_ = v_a_429_;
goto v___jp_445_;
}
case 7:
{
lean_object* v_c_457_; 
v_c_457_ = lean_ctor_get(v_e_430_, 0);
lean_inc(v_c_457_);
lean_dec_ref_known(v_e_430_, 2);
v_f_446_ = v_c_457_;
v___y_447_ = v_a_428_;
v___y_448_ = v_a_429_;
goto v___jp_445_;
}
default: 
{
lean_dec_ref(v_e_430_);
v_x_427_ = v_b_431_;
goto _start;
}
}
v___jp_432_:
{
uint8_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_unbox(v_fst_436_);
lean_dec(v_fst_436_);
v___x_439_ = lean_bool_not(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_dec(v___y_433_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_snd_437_);
lean_ctor_set(v___x_440_, 1, v___y_434_);
v_x_427_ = v_b_431_;
v_a_428_ = v___y_435_;
v_a_429_ = v___x_440_;
goto _start;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_array_push(v___y_434_, v___y_433_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_snd_437_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v_x_427_ = v_b_431_;
v_a_428_ = v___y_435_;
v_a_429_ = v___x_443_;
goto _start;
}
}
v___jp_445_:
{
lean_object* v_set_449_; lean_object* v_order_450_; uint8_t v___x_451_; 
v_set_449_ = lean_ctor_get(v___y_448_, 0);
lean_inc(v_set_449_);
v_order_450_ = lean_ctor_get(v___y_448_, 1);
lean_inc_ref(v_order_450_);
lean_dec_ref(v___y_448_);
v___x_451_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_f_446_, v_set_449_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
lean_inc(v_f_446_);
v___x_453_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_f_446_, v___x_452_, v_set_449_);
v___x_454_ = lean_box(v___x_451_);
v___y_433_ = v_f_446_;
v___y_434_ = v_order_450_;
v___y_435_ = v___y_447_;
v_fst_436_ = v___x_454_;
v_snd_437_ = v___x_453_;
goto v___jp_432_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(v___x_451_);
v___y_433_ = v_f_446_;
v___y_434_ = v_order_450_;
v___y_435_ = v___y_447_;
v_fst_436_ = v___x_455_;
v_snd_437_ = v_set_449_;
goto v___jp_432_;
}
}
}
case 1:
{
lean_object* v_v_459_; lean_object* v_b_460_; lean_object* v___x_461_; lean_object* v_snd_462_; 
v_v_459_ = lean_ctor_get(v_x_427_, 2);
lean_inc(v_v_459_);
v_b_460_ = lean_ctor_get(v_x_427_, 3);
lean_inc(v_b_460_);
lean_dec_ref_known(v_x_427_, 4);
v___x_461_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_459_, v_a_428_, v_a_429_);
v_snd_462_ = lean_ctor_get(v___x_461_, 1);
lean_inc(v_snd_462_);
lean_dec_ref(v___x_461_);
v_x_427_ = v_b_460_;
v_a_429_ = v_snd_462_;
goto _start;
}
case 9:
{
lean_object* v_cs_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_cs_464_ = lean_ctor_get(v_x_427_, 3);
lean_inc_ref(v_cs_464_);
lean_dec_ref_known(v_x_427_, 4);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_array_get_size(v_cs_464_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_nat_dec_lt(v___x_465_, v___x_466_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v_cs_464_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v_a_429_);
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_le(v___x_466_, v___x_466_);
if (v___x_470_ == 0)
{
if (v___x_468_ == 0)
{
lean_object* v___x_471_; 
lean_dec_ref(v_cs_464_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_467_);
lean_ctor_set(v___x_471_, 1, v_a_429_);
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_466_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_464_, v___x_472_, v___x_473_, v___x_467_, v_a_428_, v_a_429_);
lean_dec_ref(v_cs_464_);
return v___x_474_;
}
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((size_t)0ULL);
v___x_476_ = lean_usize_of_nat(v___x_466_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_464_, v___x_475_, v___x_476_, v___x_467_, v_a_428_, v_a_429_);
lean_dec_ref(v_cs_464_);
return v___x_477_;
}
}
}
default: 
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_IR_FnBody_isTerminal(v_x_427_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_IR_FnBody_body(v_x_427_);
lean_dec(v_x_427_);
v_x_427_ = v___x_479_;
goto _start;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_x_427_);
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_a_429_);
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; size_t v___x_495_; size_t v___x_496_; 
v___x_490_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
v___x_491_ = l_Lean_IR_Alt_body(v___x_490_);
v___x_492_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v___x_491_, v___y_487_, v___y_488_);
v_fst_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_fst_493_);
v_snd_494_ = lean_ctor_get(v___x_492_, 1);
lean_inc(v_snd_494_);
lean_dec_ref(v___x_492_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_484_, v___x_495_);
v_i_484_ = v___x_496_;
v_b_486_ = v_fst_493_;
v___y_488_ = v_snd_494_;
goto _start;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v_b_486_);
lean_ctor_set(v___x_498_, 1, v___y_488_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object* v_as_499_, lean_object* v_i_500_, lean_object* v_stop_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
size_t v_i_boxed_505_; size_t v_stop_boxed_506_; lean_object* v_res_507_; 
v_i_boxed_505_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_stop_boxed_506_ = lean_unbox_usize(v_stop_501_);
lean_dec(v_stop_501_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_499_, v_i_boxed_505_, v_stop_boxed_506_, v_b_502_, v___y_503_, v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v_as_499_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* v_x_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_508_, v_a_509_, v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_511_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_k_513_, lean_object* v_t_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_513_, v_t_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_516_, lean_object* v_k_517_, lean_object* v_t_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_516_, v_k_517_, v_t_518_);
lean_dec(v_t_518_);
lean_dec(v_k_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object* v_00_u03b2_521_, lean_object* v_k_522_, lean_object* v_v_523_, lean_object* v_t_524_, lean_object* v_hl_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_522_, v_v_523_, v_t_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* v_fn_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_530_; 
lean_inc_ref(v_a_528_);
v___x_530_ = lean_get_init_fn_name_for(v_a_528_, v_fn_527_);
if (lean_obj_tag(v___x_530_) == 1)
{
lean_object* v_val_531_; lean_object* v_set_532_; lean_object* v_order_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_556_; 
v_val_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v___x_530_, 1);
v_set_532_ = lean_ctor_get(v_a_529_, 0);
v_order_533_ = lean_ctor_get(v_a_529_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_556_ == 0)
{
v___x_535_ = v_a_529_;
v_isShared_536_ = v_isSharedCheck_556_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_order_533_);
lean_inc(v_set_532_);
lean_dec(v_a_529_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_556_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v_fst_539_; lean_object* v_snd_540_; uint8_t v___x_552_; 
v___x_537_ = lean_box(0);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_531_, v_set_532_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc(v_val_531_);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_531_, v___x_537_, v_set_532_);
v___x_554_ = lean_box(v___x_552_);
v_fst_539_ = v___x_554_;
v_snd_540_ = v___x_553_;
goto v___jp_538_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_box(v___x_552_);
v_fst_539_ = v___x_555_;
v_snd_540_ = v_set_532_;
goto v___jp_538_;
}
v___jp_538_:
{
uint8_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_unbox(v_fst_539_);
lean_dec(v_fst_539_);
v___x_542_ = lean_bool_not(v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; 
lean_dec(v_val_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v_snd_540_);
v___x_544_ = v___x_535_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_snd_540_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_order_533_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_537_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
return v___x_545_;
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_array_push(v_order_533_, v_val_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v___x_547_);
lean_ctor_set(v___x_535_, 0, v_snd_540_);
v___x_549_ = v___x_535_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_snd_540_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_547_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_537_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___x_530_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_a_529_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object* v_fn_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_559_, v_a_560_, v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v_f_566_; lean_object* v_body_567_; lean_object* v___x_568_; lean_object* v_snd_569_; lean_object* v___x_570_; 
v_f_566_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_f_566_);
v_body_567_ = lean_ctor_get(v_x_563_, 3);
lean_inc(v_body_567_);
lean_dec_ref_known(v_x_563_, 5);
v___x_568_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_566_, v_a_564_, v_a_565_);
v_snd_569_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_snd_569_);
lean_dec_ref(v___x_568_);
v___x_570_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_567_, v_a_564_, v_snd_569_);
return v___x_570_;
}
else
{
lean_object* v_f_571_; lean_object* v___x_572_; 
v_f_571_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_f_571_);
lean_dec_ref_known(v_x_563_, 4);
v___x_572_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_571_, v_a_564_, v_a_565_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object* v_x_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_573_, v_a_574_, v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
if (lean_obj_tag(v_as_577_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___y_579_);
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; lean_object* v___x_584_; lean_object* v_snd_585_; lean_object* v_set_586_; lean_object* v_order_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_611_; 
v_head_582_ = lean_ctor_get(v_as_577_, 0);
lean_inc_n(v_head_582_, 2);
v_tail_583_ = lean_ctor_get(v_as_577_, 1);
lean_inc(v_tail_583_);
lean_dec_ref_known(v_as_577_, 2);
v___x_584_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_582_, v___y_578_, v___y_579_);
v_snd_585_ = lean_ctor_get(v___x_584_, 1);
lean_inc(v_snd_585_);
lean_dec_ref(v___x_584_);
v_set_586_ = lean_ctor_get(v_snd_585_, 0);
v_order_587_ = lean_ctor_get(v_snd_585_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_snd_585_);
if (v_isSharedCheck_611_ == 0)
{
v___x_589_ = v_snd_585_;
v_isShared_590_ = v_isSharedCheck_611_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_order_587_);
lean_inc(v_set_586_);
lean_dec(v_snd_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_611_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v_fst_593_; lean_object* v_snd_594_; uint8_t v___x_606_; 
v___x_591_ = l_Lean_IR_Decl_name(v_head_582_);
lean_dec(v_head_582_);
v___x_606_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_591_, v_set_586_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
lean_inc(v___x_591_);
v___x_608_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_591_, v___x_607_, v_set_586_);
v___x_609_ = lean_box(v___x_606_);
v_fst_593_ = v___x_609_;
v_snd_594_ = v___x_608_;
goto v___jp_592_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_box(v___x_606_);
v_fst_593_ = v___x_610_;
v_snd_594_ = v_set_586_;
goto v___jp_592_;
}
v___jp_592_:
{
uint8_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unbox(v_fst_593_);
lean_dec(v_fst_593_);
v___x_596_ = lean_bool_not(v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v_snd_594_);
v___x_598_ = v___x_589_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_snd_594_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_order_587_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
v_as_577_ = v_tail_583_;
v___y_579_ = v___x_598_;
goto _start;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_array_push(v_order_587_, v___x_591_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_601_);
lean_ctor_set(v___x_589_, 0, v_snd_594_);
v___x_603_ = v___x_589_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_snd_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_601_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
v_as_577_ = v_tail_583_;
v___y_579_ = v___x_603_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object* v_as_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_as_612_, v___y_613_, v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_616_, v_a_617_, v_a_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object* v_decls_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_620_, v_a_621_, v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_627_ = l_Lean_NameSet_empty;
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_629_, lean_object* v_decls_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_snd_633_; lean_object* v_order_634_; 
v___x_631_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_632_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_630_, v_env_629_, v___x_631_);
v_snd_633_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_snd_633_);
lean_dec_ref(v___x_632_);
v_order_634_ = lean_ctor_get(v_snd_633_, 1);
lean_inc_ref(v_order_634_);
lean_dec(v_snd_633_);
return v_order_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object* v_env_635_, lean_object* v_decls_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_IR_collectUsedDecls(v_env_635_, v_decls_636_);
lean_dec_ref(v_env_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_640_, lean_object* v_t_641_, lean_object* v_x_642_){
_start:
{
lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
v_fst_643_ = lean_ctor_get(v_x_642_, 0);
v_snd_644_ = lean_ctor_get(v_x_642_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_654_ == 0)
{
v___x_646_ = v_x_642_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_snd_644_);
lean_inc(v_fst_643_);
lean_dec(v_x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_648_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_649_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_648_, v___x_649_, v_fst_643_, v_x_640_, v_t_641_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_snd_644_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
return v_x_655_;
}
else
{
lean_object* v_key_657_; lean_object* v_value_658_; lean_object* v_tail_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_682_; 
v_key_657_ = lean_ctor_get(v_x_656_, 0);
v_value_658_ = lean_ctor_get(v_x_656_, 1);
v_tail_659_ = lean_ctor_get(v_x_656_, 2);
v_isSharedCheck_682_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_682_ == 0)
{
v___x_661_ = v_x_656_;
v_isShared_662_ = v_isSharedCheck_682_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_tail_659_);
lean_inc(v_value_658_);
lean_inc(v_key_657_);
lean_dec(v_x_656_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_682_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v_fold_667_; uint64_t v___x_668_; uint64_t v___x_669_; uint64_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_663_ = lean_array_get_size(v_x_655_);
v___x_664_ = l_Lean_IR_instHashableVarId_hash(v_key_657_);
v___x_665_ = 32ULL;
v___x_666_ = lean_uint64_shift_right(v___x_664_, v___x_665_);
v_fold_667_ = lean_uint64_xor(v___x_664_, v___x_666_);
v___x_668_ = 16ULL;
v___x_669_ = lean_uint64_shift_right(v_fold_667_, v___x_668_);
v___x_670_ = lean_uint64_xor(v_fold_667_, v___x_669_);
v___x_671_ = lean_uint64_to_usize(v___x_670_);
v___x_672_ = lean_usize_of_nat(v___x_663_);
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_sub(v___x_672_, v___x_673_);
v___x_675_ = lean_usize_land(v___x_671_, v___x_674_);
v___x_676_ = lean_array_uget_borrowed(v_x_655_, v___x_675_);
lean_inc(v___x_676_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 2, v___x_676_);
v___x_678_ = v___x_661_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_key_657_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_value_658_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_676_);
v___x_678_ = v_reuseFailAlloc_681_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_array_uset(v_x_655_, v___x_675_, v___x_678_);
v_x_655_ = v___x_679_;
v_x_656_ = v_tail_659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_683_, lean_object* v_source_684_, lean_object* v_target_685_){
_start:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_get_size(v_source_684_);
v___x_687_ = lean_nat_dec_lt(v_i_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_source_684_);
lean_dec(v_i_683_);
return v_target_685_;
}
else
{
lean_object* v_es_688_; lean_object* v___x_689_; lean_object* v_source_690_; lean_object* v_target_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_es_688_ = lean_array_fget(v_source_684_, v_i_683_);
v___x_689_ = lean_box(0);
v_source_690_ = lean_array_fset(v_source_684_, v_i_683_, v___x_689_);
v_target_691_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_685_, v_es_688_);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_add(v_i_683_, v___x_692_);
lean_dec(v_i_683_);
v_i_683_ = v___x_693_;
v_source_684_ = v_source_690_;
v_target_685_ = v_target_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_nbuckets_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_696_ = lean_array_get_size(v_data_695_);
v___x_697_ = lean_unsigned_to_nat(2u);
v_nbuckets_698_ = lean_nat_mul(v___x_696_, v___x_697_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_box(0);
v___x_701_ = lean_mk_array(v_nbuckets_698_, v___x_700_);
v___x_702_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_699_, v_data_695_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
else
{
lean_object* v_key_706_; lean_object* v_tail_707_; uint8_t v___x_708_; 
v_key_706_ = lean_ctor_get(v_x_704_, 0);
v_tail_707_ = lean_ctor_get(v_x_704_, 2);
v___x_708_ = l_Lean_IR_instBEqVarId_beq(v_key_706_, v_a_703_);
if (v___x_708_ == 0)
{
v_x_704_ = v_tail_707_;
goto _start;
}
else
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_710_, lean_object* v_x_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_710_, v_x_711_);
lean_dec(v_x_711_);
lean_dec(v_a_710_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_714_, lean_object* v_b_715_, lean_object* v_x_716_){
_start:
{
if (lean_obj_tag(v_x_716_) == 0)
{
lean_dec(v_b_715_);
lean_dec(v_a_714_);
return v_x_716_;
}
else
{
lean_object* v_key_717_; lean_object* v_value_718_; lean_object* v_tail_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_731_; 
v_key_717_ = lean_ctor_get(v_x_716_, 0);
v_value_718_ = lean_ctor_get(v_x_716_, 1);
v_tail_719_ = lean_ctor_get(v_x_716_, 2);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_716_);
if (v_isSharedCheck_731_ == 0)
{
v___x_721_ = v_x_716_;
v_isShared_722_ = v_isSharedCheck_731_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_tail_719_);
lean_inc(v_value_718_);
lean_inc(v_key_717_);
lean_dec(v_x_716_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_731_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_IR_instBEqVarId_beq(v_key_717_, v_a_714_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_714_, v_b_715_, v_tail_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 2, v___x_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_key_717_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_value_718_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v___x_729_; 
lean_dec(v_value_718_);
lean_dec(v_key_717_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_b_715_);
lean_ctor_set(v___x_721_, 0, v_a_714_);
v___x_729_ = v___x_721_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_714_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_b_715_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_tail_719_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_732_, lean_object* v_a_733_, lean_object* v_b_734_){
_start:
{
lean_object* v_size_735_; lean_object* v_buckets_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_779_; 
v_size_735_ = lean_ctor_get(v_m_732_, 0);
v_buckets_736_ = lean_ctor_get(v_m_732_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_m_732_);
if (v_isSharedCheck_779_ == 0)
{
v___x_738_ = v_m_732_;
v_isShared_739_ = v_isSharedCheck_779_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_buckets_736_);
lean_inc(v_size_735_);
lean_dec(v_m_732_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_779_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; uint64_t v___x_741_; uint64_t v___x_742_; uint64_t v___x_743_; uint64_t v_fold_744_; uint64_t v___x_745_; uint64_t v___x_746_; uint64_t v___x_747_; size_t v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; size_t v___x_752_; lean_object* v_bkt_753_; uint8_t v___x_754_; 
v___x_740_ = lean_array_get_size(v_buckets_736_);
v___x_741_ = l_Lean_IR_instHashableVarId_hash(v_a_733_);
v___x_742_ = 32ULL;
v___x_743_ = lean_uint64_shift_right(v___x_741_, v___x_742_);
v_fold_744_ = lean_uint64_xor(v___x_741_, v___x_743_);
v___x_745_ = 16ULL;
v___x_746_ = lean_uint64_shift_right(v_fold_744_, v___x_745_);
v___x_747_ = lean_uint64_xor(v_fold_744_, v___x_746_);
v___x_748_ = lean_uint64_to_usize(v___x_747_);
v___x_749_ = lean_usize_of_nat(v___x_740_);
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_sub(v___x_749_, v___x_750_);
v___x_752_ = lean_usize_land(v___x_748_, v___x_751_);
v_bkt_753_ = lean_array_uget_borrowed(v_buckets_736_, v___x_752_);
v___x_754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_733_, v_bkt_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v_size_x27_756_; lean_object* v___x_757_; lean_object* v_buckets_x27_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v_size_x27_756_ = lean_nat_add(v_size_735_, v___x_755_);
lean_dec(v_size_735_);
lean_inc(v_bkt_753_);
v___x_757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_757_, 0, v_a_733_);
lean_ctor_set(v___x_757_, 1, v_b_734_);
lean_ctor_set(v___x_757_, 2, v_bkt_753_);
v_buckets_x27_758_ = lean_array_uset(v_buckets_736_, v___x_752_, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(4u);
v___x_760_ = lean_nat_mul(v_size_x27_756_, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(3u);
v___x_762_ = lean_nat_div(v___x_760_, v___x_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_array_get_size(v_buckets_x27_758_);
v___x_764_ = lean_nat_dec_le(v___x_762_, v___x_763_);
lean_dec(v___x_762_);
if (v___x_764_ == 0)
{
lean_object* v_val_765_; lean_object* v___x_767_; 
v_val_765_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_758_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v_val_765_);
lean_ctor_set(v___x_738_, 0, v_size_x27_756_);
v___x_767_ = v___x_738_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_size_x27_756_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_val_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_770_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v_buckets_x27_758_);
lean_ctor_set(v___x_738_, 0, v_size_x27_756_);
v___x_770_ = v___x_738_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_size_x27_756_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_buckets_x27_758_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v___x_772_; lean_object* v_buckets_x27_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_inc(v_bkt_753_);
v___x_772_ = lean_box(0);
v_buckets_x27_773_ = lean_array_uset(v_buckets_736_, v___x_752_, v___x_772_);
v___x_774_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_733_, v_b_734_, v_bkt_753_);
v___x_775_ = lean_array_uset(v_buckets_x27_773_, v___x_752_, v___x_774_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_775_);
v___x_777_ = v___x_738_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_size_735_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_780_, size_t v_i_781_, size_t v_stop_782_, lean_object* v_b_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_eq(v_i_781_, v_stop_782_);
if (v___x_784_ == 0)
{
lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_800_; 
v_fst_785_ = lean_ctor_get(v_b_783_, 0);
v_snd_786_ = lean_ctor_get(v_b_783_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_b_783_);
if (v_isSharedCheck_800_ == 0)
{
v___x_788_ = v_b_783_;
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_inc(v_fst_785_);
lean_dec(v_b_783_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v_x_791_; lean_object* v_ty_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_790_ = lean_array_uget_borrowed(v_as_780_, v_i_781_);
v_x_791_ = lean_ctor_get(v___x_790_, 0);
v_ty_792_ = lean_ctor_get(v___x_790_, 1);
lean_inc(v_ty_792_);
lean_inc(v_x_791_);
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_785_, v_x_791_, v_ty_792_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_793_);
v___x_795_ = v___x_788_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_786_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
size_t v___x_796_; size_t v___x_797_; 
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_781_, v___x_796_);
v_i_781_ = v___x_797_;
v_b_783_ = v___x_795_;
goto _start;
}
}
}
else
{
return v_b_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_801_, lean_object* v_i_802_, lean_object* v_stop_803_, lean_object* v_b_804_){
_start:
{
size_t v_i_boxed_805_; size_t v_stop_boxed_806_; lean_object* v_res_807_; 
v_i_boxed_805_ = lean_unbox_usize(v_i_802_);
lean_dec(v_i_802_);
v_stop_boxed_806_ = lean_unbox_usize(v_stop_803_);
lean_dec(v_stop_803_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_801_, v_i_boxed_805_, v_stop_boxed_806_, v_b_804_);
lean_dec_ref(v_as_801_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_808_, lean_object* v_s_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_array_get_size(v_ps_808_);
v___x_812_ = lean_nat_dec_lt(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
return v_s_809_;
}
else
{
uint8_t v___x_813_; 
v___x_813_ = lean_nat_dec_le(v___x_811_, v___x_811_);
if (v___x_813_ == 0)
{
if (v___x_812_ == 0)
{
return v_s_809_;
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_811_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_808_, v___x_814_, v___x_815_, v_s_809_);
return v___x_816_;
}
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_811_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_808_, v___x_817_, v___x_818_, v_s_809_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_820_, lean_object* v_s_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_IR_CollectMaps_collectParams(v_ps_820_, v_s_821_);
lean_dec_ref(v_ps_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_823_, lean_object* v_m_824_, lean_object* v_a_825_, lean_object* v_b_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_824_, v_a_825_, v_b_826_);
return v___x_827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_832_, v_a_833_, v_x_834_);
lean_dec(v_x_834_);
lean_dec(v_a_833_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_837_, lean_object* v_data_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_b_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_841_, v_b_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_845_, lean_object* v_i_846_, lean_object* v_source_847_, lean_object* v_target_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_846_, v_source_847_, v_target_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_856_, lean_object* v_xs_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_870_; 
v_fst_859_ = lean_ctor_get(v_x_858_, 0);
v_snd_860_ = lean_ctor_get(v_x_858_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_858_);
if (v_isSharedCheck_870_ == 0)
{
v___x_862_ = v_x_858_;
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_inc(v_fst_859_);
lean_dec(v_x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_870_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_864_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_865_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_864_, v___x_865_, v_snd_860_, v_j_856_, v_xs_857_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v___x_866_);
v___x_868_ = v___x_862_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_fst_859_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
uint8_t v___x_873_; 
v___x_873_ = 0;
return v___x_873_;
}
else
{
lean_object* v_key_874_; lean_object* v_tail_875_; uint8_t v___x_876_; 
v_key_874_ = lean_ctor_get(v_x_872_, 0);
v_tail_875_ = lean_ctor_get(v_x_872_, 2);
v___x_876_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_874_, v_a_871_);
if (v___x_876_ == 0)
{
v_x_872_ = v_tail_875_;
goto _start;
}
else
{
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_878_, lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_878_, v_x_879_);
lean_dec(v_x_879_);
lean_dec(v_a_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
return v_x_882_;
}
else
{
lean_object* v_key_884_; lean_object* v_value_885_; lean_object* v_tail_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_909_; 
v_key_884_ = lean_ctor_get(v_x_883_, 0);
v_value_885_ = lean_ctor_get(v_x_883_, 1);
v_tail_886_ = lean_ctor_get(v_x_883_, 2);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_909_ == 0)
{
v___x_888_ = v_x_883_;
v_isShared_889_ = v_isSharedCheck_909_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_tail_886_);
lean_inc(v_value_885_);
lean_inc(v_key_884_);
lean_dec(v_x_883_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_909_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v_fold_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_890_ = lean_array_get_size(v_x_882_);
v___x_891_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_884_);
v___x_892_ = 32ULL;
v___x_893_ = lean_uint64_shift_right(v___x_891_, v___x_892_);
v_fold_894_ = lean_uint64_xor(v___x_891_, v___x_893_);
v___x_895_ = 16ULL;
v___x_896_ = lean_uint64_shift_right(v_fold_894_, v___x_895_);
v___x_897_ = lean_uint64_xor(v_fold_894_, v___x_896_);
v___x_898_ = lean_uint64_to_usize(v___x_897_);
v___x_899_ = lean_usize_of_nat(v___x_890_);
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_sub(v___x_899_, v___x_900_);
v___x_902_ = lean_usize_land(v___x_898_, v___x_901_);
v___x_903_ = lean_array_uget_borrowed(v_x_882_, v___x_902_);
lean_inc(v___x_903_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 2, v___x_903_);
v___x_905_ = v___x_888_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_key_884_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_value_885_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_903_);
v___x_905_ = v_reuseFailAlloc_908_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = lean_array_uset(v_x_882_, v___x_902_, v___x_905_);
v_x_882_ = v___x_906_;
v_x_883_ = v_tail_886_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_910_, lean_object* v_source_911_, lean_object* v_target_912_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_array_get_size(v_source_911_);
v___x_914_ = lean_nat_dec_lt(v_i_910_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec_ref(v_source_911_);
lean_dec(v_i_910_);
return v_target_912_;
}
else
{
lean_object* v_es_915_; lean_object* v___x_916_; lean_object* v_source_917_; lean_object* v_target_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_es_915_ = lean_array_fget(v_source_911_, v_i_910_);
v___x_916_ = lean_box(0);
v_source_917_ = lean_array_fset(v_source_911_, v_i_910_, v___x_916_);
v_target_918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_912_, v_es_915_);
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_add(v_i_910_, v___x_919_);
lean_dec(v_i_910_);
v_i_910_ = v___x_920_;
v_source_911_ = v_source_917_;
v_target_912_ = v_target_918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_nbuckets_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_923_ = lean_array_get_size(v_data_922_);
v___x_924_ = lean_unsigned_to_nat(2u);
v_nbuckets_925_ = lean_nat_mul(v___x_923_, v___x_924_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_box(0);
v___x_928_ = lean_mk_array(v_nbuckets_925_, v___x_927_);
v___x_929_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_926_, v_data_922_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_930_, lean_object* v_b_931_, lean_object* v_x_932_){
_start:
{
if (lean_obj_tag(v_x_932_) == 0)
{
lean_dec(v_b_931_);
lean_dec(v_a_930_);
return v_x_932_;
}
else
{
lean_object* v_key_933_; lean_object* v_value_934_; lean_object* v_tail_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_947_; 
v_key_933_ = lean_ctor_get(v_x_932_, 0);
v_value_934_ = lean_ctor_get(v_x_932_, 1);
v_tail_935_ = lean_ctor_get(v_x_932_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_932_);
if (v_isSharedCheck_947_ == 0)
{
v___x_937_ = v_x_932_;
v_isShared_938_ = v_isSharedCheck_947_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_tail_935_);
lean_inc(v_value_934_);
lean_inc(v_key_933_);
lean_dec(v_x_932_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_947_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
uint8_t v___x_939_; 
v___x_939_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_933_, v_a_930_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_930_, v_b_931_, v_tail_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 2, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_key_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_value_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
else
{
lean_object* v___x_945_; 
lean_dec(v_value_934_);
lean_dec(v_key_933_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v_b_931_);
lean_ctor_set(v___x_937_, 0, v_a_930_);
v___x_945_ = v___x_937_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_b_931_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_tail_935_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_948_, lean_object* v_a_949_, lean_object* v_b_950_){
_start:
{
lean_object* v_size_951_; lean_object* v_buckets_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_995_; 
v_size_951_ = lean_ctor_get(v_m_948_, 0);
v_buckets_952_ = lean_ctor_get(v_m_948_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_m_948_);
if (v_isSharedCheck_995_ == 0)
{
v___x_954_ = v_m_948_;
v_isShared_955_ = v_isSharedCheck_995_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_buckets_952_);
lean_inc(v_size_951_);
lean_dec(v_m_948_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_995_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v_fold_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; size_t v___x_967_; size_t v___x_968_; lean_object* v_bkt_969_; uint8_t v___x_970_; 
v___x_956_ = lean_array_get_size(v_buckets_952_);
v___x_957_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_949_);
v___x_958_ = 32ULL;
v___x_959_ = lean_uint64_shift_right(v___x_957_, v___x_958_);
v_fold_960_ = lean_uint64_xor(v___x_957_, v___x_959_);
v___x_961_ = 16ULL;
v___x_962_ = lean_uint64_shift_right(v_fold_960_, v___x_961_);
v___x_963_ = lean_uint64_xor(v_fold_960_, v___x_962_);
v___x_964_ = lean_uint64_to_usize(v___x_963_);
v___x_965_ = lean_usize_of_nat(v___x_956_);
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_sub(v___x_965_, v___x_966_);
v___x_968_ = lean_usize_land(v___x_964_, v___x_967_);
v_bkt_969_ = lean_array_uget_borrowed(v_buckets_952_, v___x_968_);
v___x_970_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_949_, v_bkt_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v_size_x27_972_; lean_object* v___x_973_; lean_object* v_buckets_x27_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_971_ = lean_unsigned_to_nat(1u);
v_size_x27_972_ = lean_nat_add(v_size_951_, v___x_971_);
lean_dec(v_size_951_);
lean_inc(v_bkt_969_);
v___x_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_973_, 0, v_a_949_);
lean_ctor_set(v___x_973_, 1, v_b_950_);
lean_ctor_set(v___x_973_, 2, v_bkt_969_);
v_buckets_x27_974_ = lean_array_uset(v_buckets_952_, v___x_968_, v___x_973_);
v___x_975_ = lean_unsigned_to_nat(4u);
v___x_976_ = lean_nat_mul(v_size_x27_972_, v___x_975_);
v___x_977_ = lean_unsigned_to_nat(3u);
v___x_978_ = lean_nat_div(v___x_976_, v___x_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_array_get_size(v_buckets_x27_974_);
v___x_980_ = lean_nat_dec_le(v___x_978_, v___x_979_);
lean_dec(v___x_978_);
if (v___x_980_ == 0)
{
lean_object* v_val_981_; lean_object* v___x_983_; 
v_val_981_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_974_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_val_981_);
lean_ctor_set(v___x_954_, 0, v_size_x27_972_);
v___x_983_ = v___x_954_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_size_x27_972_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_val_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
lean_object* v___x_986_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_buckets_x27_974_);
lean_ctor_set(v___x_954_, 0, v_size_x27_972_);
v___x_986_ = v___x_954_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_size_x27_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_buckets_x27_974_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
else
{
lean_object* v___x_988_; lean_object* v_buckets_x27_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
lean_inc(v_bkt_969_);
v___x_988_ = lean_box(0);
v_buckets_x27_989_ = lean_array_uset(v_buckets_952_, v___x_968_, v___x_988_);
v___x_990_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_949_, v_b_950_, v_bkt_969_);
v___x_991_ = lean_array_uset(v_buckets_x27_989_, v___x_968_, v___x_990_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_991_);
v___x_993_ = v___x_954_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_size_951_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_996_, lean_object* v_a_997_){
_start:
{
switch(lean_obj_tag(v_x_996_))
{
case 0:
{
lean_object* v_x_998_; lean_object* v_ty_999_; lean_object* v_b_1000_; lean_object* v___x_1001_; lean_object* v_fst_1002_; lean_object* v_snd_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_x_998_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_x_998_);
v_ty_999_ = lean_ctor_get(v_x_996_, 1);
lean_inc(v_ty_999_);
v_b_1000_ = lean_ctor_get(v_x_996_, 3);
lean_inc(v_b_1000_);
lean_dec_ref_known(v_x_996_, 4);
v___x_1001_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1000_, v_a_997_);
v_fst_1002_ = lean_ctor_get(v___x_1001_, 0);
v_snd_1003_ = lean_ctor_get(v___x_1001_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1005_ = v___x_1001_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_snd_1003_);
lean_inc(v_fst_1002_);
lean_dec(v___x_1001_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_1002_, v_x_998_, v_ty_999_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_snd_1003_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
case 1:
{
lean_object* v_j_1012_; lean_object* v_xs_1013_; lean_object* v_v_1014_; lean_object* v_b_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_j_1012_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_j_1012_);
v_xs_1013_ = lean_ctor_get(v_x_996_, 1);
lean_inc_ref(v_xs_1013_);
v_v_1014_ = lean_ctor_get(v_x_996_, 2);
lean_inc(v_v_1014_);
v_b_1015_ = lean_ctor_get(v_x_996_, 3);
lean_inc(v_b_1015_);
lean_dec_ref_known(v_x_996_, 4);
v___x_1016_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1015_, v_a_997_);
v___x_1017_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_1014_, v___x_1016_);
v___x_1018_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1013_, v___x_1017_);
v_fst_1019_ = lean_ctor_get(v___x_1018_, 0);
v_snd_1020_ = lean_ctor_get(v___x_1018_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v___x_1018_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_snd_1020_);
lean_inc(v_fst_1019_);
lean_dec(v___x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_1020_, v_j_1012_, v_xs_1013_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_fst_1019_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
case 9:
{
lean_object* v_cs_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_cs_1029_ = lean_ctor_get(v_x_996_, 3);
lean_inc_ref(v_cs_1029_);
lean_dec_ref_known(v_x_996_, 4);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_array_get_size(v_cs_1029_);
v___x_1032_ = lean_nat_dec_lt(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_dec_ref(v_cs_1029_);
return v_a_997_;
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_nat_dec_le(v___x_1031_, v___x_1031_);
if (v___x_1033_ == 0)
{
if (v___x_1032_ == 0)
{
lean_dec_ref(v_cs_1029_);
return v_a_997_;
}
else
{
size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = lean_usize_of_nat(v___x_1031_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1029_, v___x_1034_, v___x_1035_, v_a_997_);
lean_dec_ref(v_cs_1029_);
return v___x_1036_;
}
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1031_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1029_, v___x_1037_, v___x_1038_, v_a_997_);
lean_dec_ref(v_cs_1029_);
return v___x_1039_;
}
}
}
default: 
{
uint8_t v___x_1040_; 
v___x_1040_ = l_Lean_IR_FnBody_isTerminal(v_x_996_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_IR_FnBody_body(v_x_996_);
lean_dec(v_x_996_);
v_x_996_ = v___x_1041_;
goto _start;
}
else
{
lean_dec(v_x_996_);
return v_a_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_1043_, size_t v_i_1044_, size_t v_stop_1045_, lean_object* v_b_1046_){
_start:
{
uint8_t v___x_1047_; 
v___x_1047_ = lean_usize_dec_eq(v_i_1044_, v_stop_1045_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; size_t v___x_1051_; size_t v___x_1052_; 
v___x_1048_ = lean_array_uget_borrowed(v_as_1043_, v_i_1044_);
v___x_1049_ = l_Lean_IR_Alt_body(v___x_1048_);
v___x_1050_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1049_, v_b_1046_);
v___x_1051_ = ((size_t)1ULL);
v___x_1052_ = lean_usize_add(v_i_1044_, v___x_1051_);
v_i_1044_ = v___x_1052_;
v_b_1046_ = v___x_1050_;
goto _start;
}
else
{
return v_b_1046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1054_, lean_object* v_i_1055_, lean_object* v_stop_1056_, lean_object* v_b_1057_){
_start:
{
size_t v_i_boxed_1058_; size_t v_stop_boxed_1059_; lean_object* v_res_1060_; 
v_i_boxed_1058_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_stop_boxed_1059_ = lean_unbox_usize(v_stop_1056_);
lean_dec(v_stop_1056_);
v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1054_, v_i_boxed_1058_, v_stop_boxed_1059_, v_b_1057_);
lean_dec_ref(v_as_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1061_, lean_object* v_m_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1062_, v_a_1063_, v_b_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1066_, lean_object* v_a_1067_, lean_object* v_x_1068_){
_start:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1070_, v_a_1071_, v_x_1072_);
lean_dec(v_x_1072_);
lean_dec(v_a_1071_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1075_, lean_object* v_data_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1078_, lean_object* v_a_1079_, lean_object* v_b_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1079_, v_b_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1083_, lean_object* v_i_1084_, lean_object* v_source_1085_, lean_object* v_target_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1084_, v_source_1085_, v_target_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1089_, v_x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1092_, lean_object* v_a_1093_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v_xs_1094_; lean_object* v_body_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_xs_1094_ = lean_ctor_get(v_x_1092_, 1);
lean_inc_ref(v_xs_1094_);
v_body_1095_ = lean_ctor_get(v_x_1092_, 3);
lean_inc(v_body_1095_);
lean_dec_ref_known(v_x_1092_, 5);
v___x_1096_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1095_, v_a_1093_);
v___x_1097_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1094_, v___x_1096_);
lean_dec_ref(v_xs_1094_);
return v___x_1097_;
}
else
{
lean_dec_ref(v_x_1092_);
return v_a_1093_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_unsigned_to_nat(16u);
v___x_1100_ = lean_mk_array(v___x_1099_, v___x_1098_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1108_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1106_, v___x_1107_);
return v___x_1108_;
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
