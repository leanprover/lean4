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
v___x_436_ = lean_array_push(v___y_432_, v___y_431_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_snd_434_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v_x_424_ = v_b_428_;
v_a_425_ = v___y_430_;
v_a_426_ = v___x_437_;
goto _start;
}
else
{
lean_object* v___x_439_; 
lean_dec(v___y_431_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_snd_434_);
lean_ctor_set(v___x_439_, 1, v___y_432_);
v_x_424_ = v_b_428_;
v_a_425_ = v___y_430_;
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
v___y_430_ = v___y_443_;
v___y_431_ = v_f_442_;
v___y_432_ = v_order_446_;
v_fst_433_ = v___x_450_;
v_snd_434_ = v___x_449_;
goto v___jp_429_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_box(v___x_447_);
v___y_430_ = v___y_443_;
v___y_431_ = v_f_442_;
v___y_432_ = v_order_446_;
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
lean_inc_ref(v_a_524_);
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
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object* v_fn_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_554_, v_a_555_, v_a_556_);
lean_dec_ref(v_a_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v_f_561_; lean_object* v_body_562_; lean_object* v___x_563_; lean_object* v_snd_564_; lean_object* v___x_565_; 
v_f_561_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_f_561_);
v_body_562_ = lean_ctor_get(v_x_558_, 3);
lean_inc(v_body_562_);
lean_dec_ref(v_x_558_);
v___x_563_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_561_, v_a_559_, v_a_560_);
v_snd_564_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_562_, v_a_559_, v_snd_564_);
return v___x_565_;
}
else
{
lean_object* v_f_566_; lean_object* v___x_567_; 
v_f_566_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_f_566_);
lean_dec_ref(v_x_558_);
v___x_567_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_566_, v_a_559_, v_a_560_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object* v_x_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_568_, v_a_569_, v_a_570_);
lean_dec_ref(v_a_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
if (lean_obj_tag(v_as_572_) == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_box(0);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___y_574_);
return v___x_576_;
}
else
{
lean_object* v_head_577_; lean_object* v_tail_578_; lean_object* v___x_579_; lean_object* v_snd_580_; lean_object* v_set_581_; lean_object* v_order_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_605_; 
v_head_577_ = lean_ctor_get(v_as_572_, 0);
lean_inc_n(v_head_577_, 2);
v_tail_578_ = lean_ctor_get(v_as_572_, 1);
lean_inc(v_tail_578_);
lean_dec_ref(v_as_572_);
v___x_579_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_577_, v___y_573_, v___y_574_);
v_snd_580_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_snd_580_);
lean_dec_ref(v___x_579_);
v_set_581_ = lean_ctor_get(v_snd_580_, 0);
v_order_582_ = lean_ctor_get(v_snd_580_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_snd_580_);
if (v_isSharedCheck_605_ == 0)
{
v___x_584_ = v_snd_580_;
v_isShared_585_ = v_isSharedCheck_605_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_order_582_);
lean_inc(v_set_581_);
lean_dec(v_snd_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_605_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v_fst_588_; lean_object* v_snd_589_; uint8_t v___x_600_; 
v___x_586_ = l_Lean_IR_Decl_name(v_head_577_);
lean_dec(v_head_577_);
v___x_600_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_586_, v_set_581_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
lean_inc(v___x_586_);
v___x_602_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_586_, v___x_601_, v_set_581_);
v___x_603_ = lean_box(v___x_600_);
v_fst_588_ = v___x_603_;
v_snd_589_ = v___x_602_;
goto v___jp_587_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = lean_box(v___x_600_);
v_fst_588_ = v___x_604_;
v_snd_589_ = v_set_581_;
goto v___jp_587_;
}
v___jp_587_:
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v_fst_588_);
lean_dec(v_fst_588_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_array_push(v_order_582_, v___x_586_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v___x_591_);
lean_ctor_set(v___x_584_, 0, v_snd_589_);
v___x_593_ = v___x_584_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_snd_589_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
v_as_572_ = v_tail_578_;
v___y_574_ = v___x_593_;
goto _start;
}
}
else
{
lean_object* v___x_597_; 
lean_dec(v___x_586_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v_snd_589_);
v___x_597_ = v___x_584_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_snd_589_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_order_582_);
v___x_597_ = v_reuseFailAlloc_599_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
v_as_572_ = v_tail_578_;
v___y_574_ = v___x_597_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object* v_as_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_as_606_, v___y_607_, v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_610_, v_a_611_, v_a_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object* v_decls_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_614_, v_a_615_, v_a_616_);
lean_dec_ref(v_a_615_);
return v_res_617_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_621_ = l_Lean_NameSet_empty;
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_623_, lean_object* v_decls_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_snd_627_; lean_object* v_order_628_; 
v___x_625_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_626_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_624_, v_env_623_, v___x_625_);
v_snd_627_ = lean_ctor_get(v___x_626_, 1);
lean_inc(v_snd_627_);
lean_dec_ref(v___x_626_);
v_order_628_ = lean_ctor_get(v_snd_627_, 1);
lean_inc_ref(v_order_628_);
lean_dec(v_snd_627_);
return v_order_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object* v_env_629_, lean_object* v_decls_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_IR_collectUsedDecls(v_env_629_, v_decls_630_);
lean_dec_ref(v_env_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_634_, lean_object* v_t_635_, lean_object* v_x_636_){
_start:
{
lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_648_; 
v_fst_637_ = lean_ctor_get(v_x_636_, 0);
v_snd_638_ = lean_ctor_get(v_x_636_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_648_ == 0)
{
v___x_640_ = v_x_636_;
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_inc(v_fst_637_);
lean_dec(v_x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_648_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_642_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_643_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_642_, v___x_643_, v_fst_637_, v_x_634_, v_t_635_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_644_);
v___x_646_ = v___x_640_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_snd_638_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
return v_x_649_;
}
else
{
lean_object* v_key_651_; lean_object* v_value_652_; lean_object* v_tail_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_676_; 
v_key_651_ = lean_ctor_get(v_x_650_, 0);
v_value_652_ = lean_ctor_get(v_x_650_, 1);
v_tail_653_ = lean_ctor_get(v_x_650_, 2);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_676_ == 0)
{
v___x_655_ = v_x_650_;
v_isShared_656_ = v_isSharedCheck_676_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_tail_653_);
lean_inc(v_value_652_);
lean_inc(v_key_651_);
lean_dec(v_x_650_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_676_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v_fold_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_657_ = lean_array_get_size(v_x_649_);
v___x_658_ = l_Lean_IR_instHashableVarId_hash(v_key_651_);
v___x_659_ = 32ULL;
v___x_660_ = lean_uint64_shift_right(v___x_658_, v___x_659_);
v_fold_661_ = lean_uint64_xor(v___x_658_, v___x_660_);
v___x_662_ = 16ULL;
v___x_663_ = lean_uint64_shift_right(v_fold_661_, v___x_662_);
v___x_664_ = lean_uint64_xor(v_fold_661_, v___x_663_);
v___x_665_ = lean_uint64_to_usize(v___x_664_);
v___x_666_ = lean_usize_of_nat(v___x_657_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_sub(v___x_666_, v___x_667_);
v___x_669_ = lean_usize_land(v___x_665_, v___x_668_);
v___x_670_ = lean_array_uget_borrowed(v_x_649_, v___x_669_);
lean_inc(v___x_670_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 2, v___x_670_);
v___x_672_ = v___x_655_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_key_651_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_value_652_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v___x_670_);
v___x_672_ = v_reuseFailAlloc_675_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; 
v___x_673_ = lean_array_uset(v_x_649_, v___x_669_, v___x_672_);
v_x_649_ = v___x_673_;
v_x_650_ = v_tail_653_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_677_, lean_object* v_source_678_, lean_object* v_target_679_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_array_get_size(v_source_678_);
v___x_681_ = lean_nat_dec_lt(v_i_677_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v_source_678_);
lean_dec(v_i_677_);
return v_target_679_;
}
else
{
lean_object* v_es_682_; lean_object* v___x_683_; lean_object* v_source_684_; lean_object* v_target_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_es_682_ = lean_array_fget(v_source_678_, v_i_677_);
v___x_683_ = lean_box(0);
v_source_684_ = lean_array_fset(v_source_678_, v_i_677_, v___x_683_);
v_target_685_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_679_, v_es_682_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_add(v_i_677_, v___x_686_);
lean_dec(v_i_677_);
v_i_677_ = v___x_687_;
v_source_678_ = v_source_684_;
v_target_679_ = v_target_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_nbuckets_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_690_ = lean_array_get_size(v_data_689_);
v___x_691_ = lean_unsigned_to_nat(2u);
v_nbuckets_692_ = lean_nat_mul(v___x_690_, v___x_691_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_box(0);
v___x_695_ = lean_mk_array(v_nbuckets_692_, v___x_694_);
v___x_696_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_693_, v_data_689_, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_698_) == 0)
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
else
{
lean_object* v_key_700_; lean_object* v_tail_701_; uint8_t v___x_702_; 
v_key_700_ = lean_ctor_get(v_x_698_, 0);
v_tail_701_ = lean_ctor_get(v_x_698_, 2);
v___x_702_ = l_Lean_IR_instBEqVarId_beq(v_key_700_, v_a_697_);
if (v___x_702_ == 0)
{
v_x_698_ = v_tail_701_;
goto _start;
}
else
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_704_, lean_object* v_x_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_704_, v_x_705_);
lean_dec(v_x_705_);
lean_dec(v_a_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_708_, lean_object* v_b_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
lean_dec(v_b_709_);
lean_dec(v_a_708_);
return v_x_710_;
}
else
{
lean_object* v_key_711_; lean_object* v_value_712_; lean_object* v_tail_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_725_; 
v_key_711_ = lean_ctor_get(v_x_710_, 0);
v_value_712_ = lean_ctor_get(v_x_710_, 1);
v_tail_713_ = lean_ctor_get(v_x_710_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_725_ == 0)
{
v___x_715_ = v_x_710_;
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_tail_713_);
lean_inc(v_value_712_);
lean_inc(v_key_711_);
lean_dec(v_x_710_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_725_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_IR_instBEqVarId_beq(v_key_711_, v_a_708_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_708_, v_b_709_, v_tail_713_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 2, v___x_718_);
v___x_720_ = v___x_715_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_key_711_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_value_712_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v___x_723_; 
lean_dec(v_value_712_);
lean_dec(v_key_711_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_b_709_);
lean_ctor_set(v___x_715_, 0, v_a_708_);
v___x_723_ = v___x_715_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_708_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_b_709_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_tail_713_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_726_, lean_object* v_a_727_, lean_object* v_b_728_){
_start:
{
lean_object* v_size_729_; lean_object* v_buckets_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_773_; 
v_size_729_ = lean_ctor_get(v_m_726_, 0);
v_buckets_730_ = lean_ctor_get(v_m_726_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_m_726_);
if (v_isSharedCheck_773_ == 0)
{
v___x_732_ = v_m_726_;
v_isShared_733_ = v_isSharedCheck_773_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_buckets_730_);
lean_inc(v_size_729_);
lean_dec(v_m_726_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_773_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v_fold_738_; uint64_t v___x_739_; uint64_t v___x_740_; uint64_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; lean_object* v_bkt_747_; uint8_t v___x_748_; 
v___x_734_ = lean_array_get_size(v_buckets_730_);
v___x_735_ = l_Lean_IR_instHashableVarId_hash(v_a_727_);
v___x_736_ = 32ULL;
v___x_737_ = lean_uint64_shift_right(v___x_735_, v___x_736_);
v_fold_738_ = lean_uint64_xor(v___x_735_, v___x_737_);
v___x_739_ = 16ULL;
v___x_740_ = lean_uint64_shift_right(v_fold_738_, v___x_739_);
v___x_741_ = lean_uint64_xor(v_fold_738_, v___x_740_);
v___x_742_ = lean_uint64_to_usize(v___x_741_);
v___x_743_ = lean_usize_of_nat(v___x_734_);
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_sub(v___x_743_, v___x_744_);
v___x_746_ = lean_usize_land(v___x_742_, v___x_745_);
v_bkt_747_ = lean_array_uget_borrowed(v_buckets_730_, v___x_746_);
v___x_748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_727_, v_bkt_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v_size_x27_750_; lean_object* v___x_751_; lean_object* v_buckets_x27_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_749_ = lean_unsigned_to_nat(1u);
v_size_x27_750_ = lean_nat_add(v_size_729_, v___x_749_);
lean_dec(v_size_729_);
lean_inc(v_bkt_747_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v_a_727_);
lean_ctor_set(v___x_751_, 1, v_b_728_);
lean_ctor_set(v___x_751_, 2, v_bkt_747_);
v_buckets_x27_752_ = lean_array_uset(v_buckets_730_, v___x_746_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(4u);
v___x_754_ = lean_nat_mul(v_size_x27_750_, v___x_753_);
v___x_755_ = lean_unsigned_to_nat(3u);
v___x_756_ = lean_nat_div(v___x_754_, v___x_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_array_get_size(v_buckets_x27_752_);
v___x_758_ = lean_nat_dec_le(v___x_756_, v___x_757_);
lean_dec(v___x_756_);
if (v___x_758_ == 0)
{
lean_object* v_val_759_; lean_object* v___x_761_; 
v_val_759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_752_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v_val_759_);
lean_ctor_set(v___x_732_, 0, v_size_x27_750_);
v___x_761_ = v___x_732_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_size_x27_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_val_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
else
{
lean_object* v___x_764_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v_buckets_x27_752_);
lean_ctor_set(v___x_732_, 0, v_size_x27_750_);
v___x_764_ = v___x_732_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_size_x27_750_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_buckets_x27_752_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_object* v___x_766_; lean_object* v_buckets_x27_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
lean_inc(v_bkt_747_);
v___x_766_ = lean_box(0);
v_buckets_x27_767_ = lean_array_uset(v_buckets_730_, v___x_746_, v___x_766_);
v___x_768_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_727_, v_b_728_, v_bkt_747_);
v___x_769_ = lean_array_uset(v_buckets_x27_767_, v___x_746_, v___x_768_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_769_);
v___x_771_ = v___x_732_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_size_729_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_774_, size_t v_i_775_, size_t v_stop_776_, lean_object* v_b_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_eq(v_i_775_, v_stop_776_);
if (v___x_778_ == 0)
{
lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_794_; 
v_fst_779_ = lean_ctor_get(v_b_777_, 0);
v_snd_780_ = lean_ctor_get(v_b_777_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_b_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_782_ = v_b_777_;
v_isShared_783_ = v_isSharedCheck_794_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_inc(v_fst_779_);
lean_dec(v_b_777_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_794_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v_x_785_; lean_object* v_ty_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_784_ = lean_array_uget_borrowed(v_as_774_, v_i_775_);
v_x_785_ = lean_ctor_get(v___x_784_, 0);
v_ty_786_ = lean_ctor_get(v___x_784_, 1);
lean_inc(v_ty_786_);
lean_inc(v_x_785_);
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_779_, v_x_785_, v_ty_786_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_787_);
v___x_789_ = v___x_782_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_snd_780_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
size_t v___x_790_; size_t v___x_791_; 
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_add(v_i_775_, v___x_790_);
v_i_775_ = v___x_791_;
v_b_777_ = v___x_789_;
goto _start;
}
}
}
else
{
return v_b_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_795_, lean_object* v_i_796_, lean_object* v_stop_797_, lean_object* v_b_798_){
_start:
{
size_t v_i_boxed_799_; size_t v_stop_boxed_800_; lean_object* v_res_801_; 
v_i_boxed_799_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_stop_boxed_800_ = lean_unbox_usize(v_stop_797_);
lean_dec(v_stop_797_);
v_res_801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_795_, v_i_boxed_799_, v_stop_boxed_800_, v_b_798_);
lean_dec_ref(v_as_795_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_802_, lean_object* v_s_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v_ps_802_);
v___x_806_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
return v_s_803_;
}
else
{
uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_le(v___x_805_, v___x_805_);
if (v___x_807_ == 0)
{
if (v___x_806_ == 0)
{
return v_s_803_;
}
else
{
size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((size_t)0ULL);
v___x_809_ = lean_usize_of_nat(v___x_805_);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_802_, v___x_808_, v___x_809_, v_s_803_);
return v___x_810_;
}
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_805_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_802_, v___x_811_, v___x_812_, v_s_803_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_814_, lean_object* v_s_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_IR_CollectMaps_collectParams(v_ps_814_, v_s_815_);
lean_dec_ref(v_ps_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_817_, lean_object* v_m_818_, lean_object* v_a_819_, lean_object* v_b_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_818_, v_a_819_, v_b_820_);
return v___x_821_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_822_, lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_823_, v_x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_826_, lean_object* v_a_827_, lean_object* v_x_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_826_, v_a_827_, v_x_828_);
lean_dec(v_x_828_);
lean_dec(v_a_827_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_831_, lean_object* v_data_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_834_, lean_object* v_a_835_, lean_object* v_b_836_, lean_object* v_x_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_835_, v_b_836_, v_x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_839_, lean_object* v_i_840_, lean_object* v_source_841_, lean_object* v_target_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_840_, v_source_841_, v_target_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_850_, lean_object* v_xs_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_fst_853_; lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v_fst_853_ = lean_ctor_get(v_x_852_, 0);
v_snd_854_ = lean_ctor_get(v_x_852_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_852_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v_x_852_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_inc(v_fst_853_);
lean_dec(v_x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_858_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_859_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_858_, v___x_859_, v_snd_854_, v_j_850_, v_xs_851_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_865_, lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 0)
{
uint8_t v___x_867_; 
v___x_867_ = 0;
return v___x_867_;
}
else
{
lean_object* v_key_868_; lean_object* v_tail_869_; uint8_t v___x_870_; 
v_key_868_ = lean_ctor_get(v_x_866_, 0);
v_tail_869_ = lean_ctor_get(v_x_866_, 2);
v___x_870_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_868_, v_a_865_);
if (v___x_870_ == 0)
{
v_x_866_ = v_tail_869_;
goto _start;
}
else
{
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_872_, lean_object* v_x_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_872_, v_x_873_);
lean_dec(v_x_873_);
lean_dec(v_a_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
return v_x_876_;
}
else
{
lean_object* v_key_878_; lean_object* v_value_879_; lean_object* v_tail_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_903_; 
v_key_878_ = lean_ctor_get(v_x_877_, 0);
v_value_879_ = lean_ctor_get(v_x_877_, 1);
v_tail_880_ = lean_ctor_get(v_x_877_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_903_ == 0)
{
v___x_882_ = v_x_877_;
v_isShared_883_ = v_isSharedCheck_903_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_tail_880_);
lean_inc(v_value_879_);
lean_inc(v_key_878_);
lean_dec(v_x_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_903_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v_fold_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_884_ = lean_array_get_size(v_x_876_);
v___x_885_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_878_);
v___x_886_ = 32ULL;
v___x_887_ = lean_uint64_shift_right(v___x_885_, v___x_886_);
v_fold_888_ = lean_uint64_xor(v___x_885_, v___x_887_);
v___x_889_ = 16ULL;
v___x_890_ = lean_uint64_shift_right(v_fold_888_, v___x_889_);
v___x_891_ = lean_uint64_xor(v_fold_888_, v___x_890_);
v___x_892_ = lean_uint64_to_usize(v___x_891_);
v___x_893_ = lean_usize_of_nat(v___x_884_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_sub(v___x_893_, v___x_894_);
v___x_896_ = lean_usize_land(v___x_892_, v___x_895_);
v___x_897_ = lean_array_uget_borrowed(v_x_876_, v___x_896_);
lean_inc(v___x_897_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 2, v___x_897_);
v___x_899_ = v___x_882_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_key_878_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_value_879_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v___x_897_);
v___x_899_ = v_reuseFailAlloc_902_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = lean_array_uset(v_x_876_, v___x_896_, v___x_899_);
v_x_876_ = v___x_900_;
v_x_877_ = v_tail_880_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_904_, lean_object* v_source_905_, lean_object* v_target_906_){
_start:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_array_get_size(v_source_905_);
v___x_908_ = lean_nat_dec_lt(v_i_904_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v_source_905_);
lean_dec(v_i_904_);
return v_target_906_;
}
else
{
lean_object* v_es_909_; lean_object* v___x_910_; lean_object* v_source_911_; lean_object* v_target_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_es_909_ = lean_array_fget(v_source_905_, v_i_904_);
v___x_910_ = lean_box(0);
v_source_911_ = lean_array_fset(v_source_905_, v_i_904_, v___x_910_);
v_target_912_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_906_, v_es_909_);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_nat_add(v_i_904_, v___x_913_);
lean_dec(v_i_904_);
v_i_904_ = v___x_914_;
v_source_905_ = v_source_911_;
v_target_906_ = v_target_912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_nbuckets_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_917_ = lean_array_get_size(v_data_916_);
v___x_918_ = lean_unsigned_to_nat(2u);
v_nbuckets_919_ = lean_nat_mul(v___x_917_, v___x_918_);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_box(0);
v___x_922_ = lean_mk_array(v_nbuckets_919_, v___x_921_);
v___x_923_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_920_, v_data_916_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_924_, lean_object* v_b_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_dec(v_b_925_);
lean_dec(v_a_924_);
return v_x_926_;
}
else
{
lean_object* v_key_927_; lean_object* v_value_928_; lean_object* v_tail_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_941_; 
v_key_927_ = lean_ctor_get(v_x_926_, 0);
v_value_928_ = lean_ctor_get(v_x_926_, 1);
v_tail_929_ = lean_ctor_get(v_x_926_, 2);
v_isSharedCheck_941_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_941_ == 0)
{
v___x_931_ = v_x_926_;
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_tail_929_);
lean_inc(v_value_928_);
lean_inc(v_key_927_);
lean_dec(v_x_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_941_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_927_, v_a_924_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_924_, v_b_925_, v_tail_929_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v___x_934_);
v___x_936_ = v___x_931_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_key_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_value_928_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
lean_object* v___x_939_; 
lean_dec(v_value_928_);
lean_dec(v_key_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_b_925_);
lean_ctor_set(v___x_931_, 0, v_a_924_);
v___x_939_ = v___x_931_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_924_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_b_925_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_tail_929_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_942_, lean_object* v_a_943_, lean_object* v_b_944_){
_start:
{
lean_object* v_size_945_; lean_object* v_buckets_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_989_; 
v_size_945_ = lean_ctor_get(v_m_942_, 0);
v_buckets_946_ = lean_ctor_get(v_m_942_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_m_942_);
if (v_isSharedCheck_989_ == 0)
{
v___x_948_ = v_m_942_;
v_isShared_949_ = v_isSharedCheck_989_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_buckets_946_);
lean_inc(v_size_945_);
lean_dec(v_m_942_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_989_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; uint64_t v___x_951_; uint64_t v___x_952_; uint64_t v___x_953_; uint64_t v_fold_954_; uint64_t v___x_955_; uint64_t v___x_956_; uint64_t v___x_957_; size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; size_t v___x_962_; lean_object* v_bkt_963_; uint8_t v___x_964_; 
v___x_950_ = lean_array_get_size(v_buckets_946_);
v___x_951_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_943_);
v___x_952_ = 32ULL;
v___x_953_ = lean_uint64_shift_right(v___x_951_, v___x_952_);
v_fold_954_ = lean_uint64_xor(v___x_951_, v___x_953_);
v___x_955_ = 16ULL;
v___x_956_ = lean_uint64_shift_right(v_fold_954_, v___x_955_);
v___x_957_ = lean_uint64_xor(v_fold_954_, v___x_956_);
v___x_958_ = lean_uint64_to_usize(v___x_957_);
v___x_959_ = lean_usize_of_nat(v___x_950_);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_sub(v___x_959_, v___x_960_);
v___x_962_ = lean_usize_land(v___x_958_, v___x_961_);
v_bkt_963_ = lean_array_uget_borrowed(v_buckets_946_, v___x_962_);
v___x_964_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_943_, v_bkt_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v_size_x27_966_; lean_object* v___x_967_; lean_object* v_buckets_x27_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v_size_x27_966_ = lean_nat_add(v_size_945_, v___x_965_);
lean_dec(v_size_945_);
lean_inc(v_bkt_963_);
v___x_967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_967_, 0, v_a_943_);
lean_ctor_set(v___x_967_, 1, v_b_944_);
lean_ctor_set(v___x_967_, 2, v_bkt_963_);
v_buckets_x27_968_ = lean_array_uset(v_buckets_946_, v___x_962_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(4u);
v___x_970_ = lean_nat_mul(v_size_x27_966_, v___x_969_);
v___x_971_ = lean_unsigned_to_nat(3u);
v___x_972_ = lean_nat_div(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_array_get_size(v_buckets_x27_968_);
v___x_974_ = lean_nat_dec_le(v___x_972_, v___x_973_);
lean_dec(v___x_972_);
if (v___x_974_ == 0)
{
lean_object* v_val_975_; lean_object* v___x_977_; 
v_val_975_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_968_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_val_975_);
lean_ctor_set(v___x_948_, 0, v_size_x27_966_);
v___x_977_ = v___x_948_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_size_x27_966_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_val_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
else
{
lean_object* v___x_980_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_buckets_x27_968_);
lean_ctor_set(v___x_948_, 0, v_size_x27_966_);
v___x_980_ = v___x_948_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_size_x27_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_buckets_x27_968_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
lean_object* v___x_982_; lean_object* v_buckets_x27_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
lean_inc(v_bkt_963_);
v___x_982_ = lean_box(0);
v_buckets_x27_983_ = lean_array_uset(v_buckets_946_, v___x_962_, v___x_982_);
v___x_984_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_943_, v_b_944_, v_bkt_963_);
v___x_985_ = lean_array_uset(v_buckets_x27_983_, v___x_962_, v___x_984_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_985_);
v___x_987_ = v___x_948_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_size_945_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_990_, lean_object* v_a_991_){
_start:
{
switch(lean_obj_tag(v_x_990_))
{
case 0:
{
lean_object* v_x_992_; lean_object* v_ty_993_; lean_object* v_b_994_; lean_object* v___x_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
v_x_992_ = lean_ctor_get(v_x_990_, 0);
lean_inc(v_x_992_);
v_ty_993_ = lean_ctor_get(v_x_990_, 1);
lean_inc(v_ty_993_);
v_b_994_ = lean_ctor_get(v_x_990_, 3);
lean_inc(v_b_994_);
lean_dec_ref(v_x_990_);
v___x_995_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_994_, v_a_991_);
v_fst_996_ = lean_ctor_get(v___x_995_, 0);
v_snd_997_ = lean_ctor_get(v___x_995_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_999_ = v___x_995_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_inc(v_fst_996_);
lean_dec(v___x_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_996_, v_x_992_, v_ty_993_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_snd_997_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
case 1:
{
lean_object* v_j_1006_; lean_object* v_xs_1007_; lean_object* v_v_1008_; lean_object* v_b_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_fst_1013_; lean_object* v_snd_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_j_1006_ = lean_ctor_get(v_x_990_, 0);
lean_inc(v_j_1006_);
v_xs_1007_ = lean_ctor_get(v_x_990_, 1);
lean_inc_ref(v_xs_1007_);
v_v_1008_ = lean_ctor_get(v_x_990_, 2);
lean_inc(v_v_1008_);
v_b_1009_ = lean_ctor_get(v_x_990_, 3);
lean_inc(v_b_1009_);
lean_dec_ref(v_x_990_);
v___x_1010_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1009_, v_a_991_);
v___x_1011_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_1008_, v___x_1010_);
v___x_1012_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1007_, v___x_1011_);
v_fst_1013_ = lean_ctor_get(v___x_1012_, 0);
v_snd_1014_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v___x_1012_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_snd_1014_);
lean_inc(v_fst_1013_);
lean_dec(v___x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_1014_, v_j_1006_, v_xs_1007_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_fst_1013_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
case 9:
{
lean_object* v_cs_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_cs_1023_ = lean_ctor_get(v_x_990_, 3);
lean_inc_ref(v_cs_1023_);
lean_dec_ref(v_x_990_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_cs_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec_ref(v_cs_1023_);
return v_a_991_;
}
else
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_nat_dec_le(v___x_1025_, v___x_1025_);
if (v___x_1027_ == 0)
{
if (v___x_1026_ == 0)
{
lean_dec_ref(v_cs_1023_);
return v_a_991_;
}
else
{
size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = lean_usize_of_nat(v___x_1025_);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1023_, v___x_1028_, v___x_1029_, v_a_991_);
lean_dec_ref(v_cs_1023_);
return v___x_1030_;
}
}
else
{
size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = lean_usize_of_nat(v___x_1025_);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1023_, v___x_1031_, v___x_1032_, v_a_991_);
lean_dec_ref(v_cs_1023_);
return v___x_1033_;
}
}
}
default: 
{
uint8_t v___x_1034_; 
v___x_1034_ = l_Lean_IR_FnBody_isTerminal(v_x_990_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_IR_FnBody_body(v_x_990_);
lean_dec(v_x_990_);
v_x_990_ = v___x_1035_;
goto _start;
}
else
{
lean_dec(v_x_990_);
return v_a_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_1037_, size_t v_i_1038_, size_t v_stop_1039_, lean_object* v_b_1040_){
_start:
{
uint8_t v___x_1041_; 
v___x_1041_ = lean_usize_dec_eq(v_i_1038_, v_stop_1039_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; 
v___x_1042_ = lean_array_uget_borrowed(v_as_1037_, v_i_1038_);
v___x_1043_ = l_Lean_IR_Alt_body(v___x_1042_);
v___x_1044_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1043_, v_b_1040_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_1038_, v___x_1045_);
v_i_1038_ = v___x_1046_;
v_b_1040_ = v___x_1044_;
goto _start;
}
else
{
return v_b_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1048_, lean_object* v_i_1049_, lean_object* v_stop_1050_, lean_object* v_b_1051_){
_start:
{
size_t v_i_boxed_1052_; size_t v_stop_boxed_1053_; lean_object* v_res_1054_; 
v_i_boxed_1052_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_stop_boxed_1053_ = lean_unbox_usize(v_stop_1050_);
lean_dec(v_stop_1050_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1048_, v_i_boxed_1052_, v_stop_boxed_1053_, v_b_1051_);
lean_dec_ref(v_as_1048_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1055_, lean_object* v_m_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1056_, v_a_1057_, v_b_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1061_, v_x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1064_, lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1064_, v_a_1065_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec(v_a_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1069_, lean_object* v_data_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1073_, v_b_1074_, v_x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1077_, lean_object* v_i_1078_, lean_object* v_source_1079_, lean_object* v_target_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1078_, v_source_1079_, v_target_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1086_, lean_object* v_a_1087_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v_xs_1088_; lean_object* v_body_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_xs_1088_ = lean_ctor_get(v_x_1086_, 1);
lean_inc_ref(v_xs_1088_);
v_body_1089_ = lean_ctor_get(v_x_1086_, 3);
lean_inc(v_body_1089_);
lean_dec_ref(v_x_1086_);
v___x_1090_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1089_, v_a_1087_);
v___x_1091_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1088_, v___x_1090_);
lean_dec_ref(v_xs_1088_);
return v___x_1091_;
}
else
{
lean_dec_ref(v_x_1086_);
return v_a_1087_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_unsigned_to_nat(16u);
v___x_1094_ = lean_mk_array(v___x_1093_, v___x_1092_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1095_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1102_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1100_, v___x_1101_);
return v___x_1102_;
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
