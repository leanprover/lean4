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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
uint8_t v___x_27_; 
v___x_27_ = lean_usize_dec_eq(v_i_21_, v_stop_22_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v_toImport_29_; uint8_t v_irPhases_30_; uint8_t v___x_31_; uint8_t v___x_32_; 
v___x_28_ = lean_array_uget_borrowed(v_as_20_, v_i_21_);
v_toImport_29_ = lean_ctor_get(v___x_28_, 0);
v_irPhases_30_ = lean_ctor_get_uint8(v___x_28_, sizeof(void*)*1);
v___x_31_ = 1;
v___x_32_ = l_Lean_instBEqIRPhases_beq(v_irPhases_30_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v_module_33_; uint8_t v___x_34_; 
v_module_33_ = lean_ctor_get(v_toImport_29_, 0);
v___x_34_ = l_Lean_Name_isPrefixOf(v_modulePrefix_19_, v_module_33_);
if (v___x_34_ == 0)
{
goto v___jp_23_;
}
else
{
return v___x_34_;
}
}
else
{
goto v___jp_23_;
}
}
else
{
uint8_t v___x_35_; 
v___x_35_ = 0;
return v___x_35_;
}
v___jp_23_:
{
size_t v___x_24_; size_t v___x_25_; 
v___x_24_ = ((size_t)1ULL);
v___x_25_ = lean_usize_add(v_i_21_, v___x_24_);
v_i_21_ = v___x_25_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_36_, lean_object* v_as_37_, lean_object* v_i_38_, lean_object* v_stop_39_){
_start:
{
size_t v_i_boxed_40_; size_t v_stop_boxed_41_; uint8_t v_res_42_; lean_object* v_r_43_; 
v_i_boxed_40_ = lean_unbox_usize(v_i_38_);
lean_dec(v_i_38_);
v_stop_boxed_41_ = lean_unbox_usize(v_stop_39_);
lean_dec(v_stop_39_);
v_res_42_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_36_, v_as_37_, v_i_boxed_40_, v_stop_boxed_41_);
lean_dec_ref(v_as_37_);
lean_dec(v_modulePrefix_36_);
v_r_43_ = lean_box(v_res_42_);
return v_r_43_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_usesModuleFrom(lean_object* v_env_44_, lean_object* v_modulePrefix_45_){
_start:
{
lean_object* v___x_46_; lean_object* v_modules_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_46_ = l_Lean_Environment_header(v_env_44_);
v_modules_47_ = lean_ctor_get(v___x_46_, 3);
lean_inc_ref(v_modules_47_);
lean_dec_ref(v___x_46_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_array_get_size(v_modules_47_);
v___x_50_ = lean_nat_dec_lt(v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
lean_dec_ref(v_modules_47_);
return v___x_50_;
}
else
{
if (v___x_50_ == 0)
{
lean_dec_ref(v_modules_47_);
return v___x_50_;
}
else
{
size_t v___x_51_; size_t v___x_52_; uint8_t v___x_53_; 
v___x_51_ = ((size_t)0ULL);
v___x_52_ = lean_usize_of_nat(v___x_49_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_45_, v_modules_47_, v___x_51_, v___x_52_);
lean_dec_ref(v_modules_47_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_usesModuleFrom___boxed(lean_object* v_env_54_, lean_object* v_modulePrefix_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_IR_usesModuleFrom(v_env_54_, v_modulePrefix_55_);
lean_dec(v_modulePrefix_55_);
lean_dec_ref(v_env_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___redArg(lean_object* v_f_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_set_61_; lean_object* v_order_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_85_; 
v_set_61_ = lean_ctor_get(v_a_60_, 0);
v_order_62_ = lean_ctor_get(v_a_60_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_a_60_);
if (v_isSharedCheck_85_ == 0)
{
v___x_64_ = v_a_60_;
v_isShared_65_ = v_isSharedCheck_85_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_order_62_);
lean_inc(v_set_61_);
lean_dec(v_a_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_85_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v_fst_68_; lean_object* v_snd_69_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_66_ = lean_box(0);
v___x_80_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_61_);
lean_inc(v_f_59_);
v___x_81_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_80_, v_f_59_, v_set_61_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc(v_f_59_);
v___x_82_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_80_, v_f_59_, v___x_66_, v_set_61_);
v___x_83_ = lean_box(v___x_81_);
v_fst_68_ = v___x_83_;
v_snd_69_ = v___x_82_;
goto v___jp_67_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(v___x_81_);
v_fst_68_ = v___x_84_;
v_snd_69_ = v_set_61_;
goto v___jp_67_;
}
v___jp_67_:
{
uint8_t v___x_70_; 
v___x_70_ = lean_unbox(v_fst_68_);
lean_dec(v_fst_68_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_array_push(v_order_62_, v_f_59_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_71_);
lean_ctor_set(v___x_64_, 0, v_snd_69_);
v___x_73_ = v___x_64_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_snd_69_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_75_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_66_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
return v___x_74_;
}
}
else
{
lean_object* v___x_77_; 
lean_dec(v_f_59_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v_snd_69_);
v___x_77_ = v___x_64_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_snd_69_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_order_62_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_66_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* v_f_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_set_89_; lean_object* v_order_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_113_; 
v_set_89_ = lean_ctor_get(v_a_88_, 0);
v_order_90_ = lean_ctor_get(v_a_88_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_a_88_);
if (v_isSharedCheck_113_ == 0)
{
v___x_92_ = v_a_88_;
v_isShared_93_ = v_isSharedCheck_113_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_order_90_);
lean_inc(v_set_89_);
lean_dec(v_a_88_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_113_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v_fst_96_; lean_object* v_snd_97_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_94_ = lean_box(0);
v___x_108_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_89_);
lean_inc(v_f_86_);
v___x_109_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_108_, v_f_86_, v_set_89_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_inc(v_f_86_);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_108_, v_f_86_, v___x_94_, v_set_89_);
v___x_111_ = lean_box(v___x_109_);
v_fst_96_ = v___x_111_;
v_snd_97_ = v___x_110_;
goto v___jp_95_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(v___x_109_);
v_fst_96_ = v___x_112_;
v_snd_97_ = v_set_89_;
goto v___jp_95_;
}
v___jp_95_:
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v_fst_96_);
lean_dec(v_fst_96_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_array_push(v_order_90_, v_f_86_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___x_99_);
lean_ctor_set(v___x_92_, 0, v_snd_97_);
v___x_101_ = v___x_92_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_snd_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_94_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
return v___x_102_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec(v_f_86_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v_snd_97_);
v___x_105_ = v___x_92_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_snd_97_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_order_90_);
v___x_105_ = v_reuseFailAlloc_107_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_94_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
return v___x_106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* v_f_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_IR_CollectUsedDecls_collect(v_f_114_, v_a_115_, v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object* v_k_118_, lean_object* v_v_119_, lean_object* v_t_120_){
_start:
{
if (lean_obj_tag(v_t_120_) == 0)
{
lean_object* v_size_121_; lean_object* v_k_122_; lean_object* v_v_123_; lean_object* v_l_124_; lean_object* v_r_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_405_; 
v_size_121_ = lean_ctor_get(v_t_120_, 0);
v_k_122_ = lean_ctor_get(v_t_120_, 1);
v_v_123_ = lean_ctor_get(v_t_120_, 2);
v_l_124_ = lean_ctor_get(v_t_120_, 3);
v_r_125_ = lean_ctor_get(v_t_120_, 4);
v_isSharedCheck_405_ = !lean_is_exclusive(v_t_120_);
if (v_isSharedCheck_405_ == 0)
{
v___x_127_ = v_t_120_;
v_isShared_128_ = v_isSharedCheck_405_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_r_125_);
lean_inc(v_l_124_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
lean_inc(v_size_121_);
lean_dec(v_t_120_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_405_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___x_129_; 
v___x_129_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_118_, v_k_122_);
switch(v___x_129_)
{
case 0:
{
lean_object* v_impl_130_; lean_object* v___x_131_; 
lean_dec(v_size_121_);
v_impl_130_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_118_, v_v_119_, v_l_124_);
v___x_131_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_125_) == 0)
{
lean_object* v_size_132_; lean_object* v_size_133_; lean_object* v_k_134_; lean_object* v_v_135_; lean_object* v_l_136_; lean_object* v_r_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_size_132_ = lean_ctor_get(v_r_125_, 0);
v_size_133_ = lean_ctor_get(v_impl_130_, 0);
lean_inc(v_size_133_);
v_k_134_ = lean_ctor_get(v_impl_130_, 1);
lean_inc(v_k_134_);
v_v_135_ = lean_ctor_get(v_impl_130_, 2);
lean_inc(v_v_135_);
v_l_136_ = lean_ctor_get(v_impl_130_, 3);
lean_inc(v_l_136_);
v_r_137_ = lean_ctor_get(v_impl_130_, 4);
lean_inc(v_r_137_);
v___x_138_ = lean_unsigned_to_nat(3u);
v___x_139_ = lean_nat_mul(v___x_138_, v_size_132_);
v___x_140_ = lean_nat_dec_lt(v___x_139_, v_size_133_);
lean_dec(v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
lean_dec(v_r_137_);
lean_dec(v_l_136_);
lean_dec(v_v_135_);
lean_dec(v_k_134_);
v___x_141_ = lean_nat_add(v___x_131_, v_size_133_);
lean_dec(v_size_133_);
v___x_142_ = lean_nat_add(v___x_141_, v_size_132_);
lean_dec(v___x_141_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 3, v_impl_130_);
lean_ctor_set(v___x_127_, 0, v___x_142_);
v___x_144_ = v___x_127_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_impl_130_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v_r_125_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
else
{
lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_211_; 
v_isSharedCheck_211_ = !lean_is_exclusive(v_impl_130_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_212_ = lean_ctor_get(v_impl_130_, 4);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_impl_130_, 3);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_impl_130_, 2);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_impl_130_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_impl_130_, 0);
lean_dec(v_unused_216_);
v___x_147_ = v_impl_130_;
v_isShared_148_ = v_isSharedCheck_211_;
goto v_resetjp_146_;
}
else
{
lean_dec(v_impl_130_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_211_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_size_149_; lean_object* v_size_150_; lean_object* v_k_151_; lean_object* v_v_152_; lean_object* v_l_153_; lean_object* v_r_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_size_149_ = lean_ctor_get(v_l_136_, 0);
v_size_150_ = lean_ctor_get(v_r_137_, 0);
v_k_151_ = lean_ctor_get(v_r_137_, 1);
v_v_152_ = lean_ctor_get(v_r_137_, 2);
v_l_153_ = lean_ctor_get(v_r_137_, 3);
v_r_154_ = lean_ctor_get(v_r_137_, 4);
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = lean_nat_mul(v___x_155_, v_size_149_);
v___x_157_ = lean_nat_dec_lt(v_size_150_, v___x_156_);
lean_dec(v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_186_; 
lean_inc(v_r_154_);
lean_inc(v_l_153_);
lean_inc(v_v_152_);
lean_inc(v_k_151_);
v_isSharedCheck_186_ = !lean_is_exclusive(v_r_137_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; 
v_unused_187_ = lean_ctor_get(v_r_137_, 4);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_r_137_, 3);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_r_137_, 2);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_r_137_, 1);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_r_137_, 0);
lean_dec(v_unused_191_);
v___x_159_ = v_r_137_;
v_isShared_160_ = v_isSharedCheck_186_;
goto v_resetjp_158_;
}
else
{
lean_dec(v_r_137_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_186_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___x_174_; lean_object* v___y_176_; 
v___x_161_ = lean_nat_add(v___x_131_, v_size_133_);
lean_dec(v_size_133_);
v___x_162_ = lean_nat_add(v___x_161_, v_size_132_);
lean_dec(v___x_161_);
v___x_174_ = lean_nat_add(v___x_131_, v_size_149_);
if (lean_obj_tag(v_l_153_) == 0)
{
lean_object* v_size_184_; 
v_size_184_ = lean_ctor_get(v_l_153_, 0);
lean_inc(v_size_184_);
v___y_176_ = v_size_184_;
goto v___jp_175_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___y_176_ = v___x_185_;
goto v___jp_175_;
}
v___jp_163_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_nat_add(v___y_164_, v___y_166_);
lean_dec(v___y_166_);
lean_dec(v___y_164_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 4, v_r_125_);
lean_ctor_set(v___x_159_, 3, v_r_154_);
lean_ctor_set(v___x_159_, 2, v_v_123_);
lean_ctor_set(v___x_159_, 1, v_k_122_);
lean_ctor_set(v___x_159_, 0, v___x_167_);
v___x_169_ = v___x_159_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_r_154_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_r_125_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 4, v___x_169_);
lean_ctor_set(v___x_147_, 3, v___y_165_);
lean_ctor_set(v___x_147_, 2, v_v_152_);
lean_ctor_set(v___x_147_, 1, v_k_151_);
lean_ctor_set(v___x_147_, 0, v___x_162_);
v___x_171_ = v___x_147_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_k_151_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_v_152_);
lean_ctor_set(v_reuseFailAlloc_172_, 3, v___y_165_);
lean_ctor_set(v_reuseFailAlloc_172_, 4, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_nat_add(v___x_174_, v___y_176_);
lean_dec(v___y_176_);
lean_dec(v___x_174_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v_l_153_);
lean_ctor_set(v___x_127_, 3, v_l_136_);
lean_ctor_set(v___x_127_, 2, v_v_135_);
lean_ctor_set(v___x_127_, 1, v_k_134_);
lean_ctor_set(v___x_127_, 0, v___x_177_);
v___x_179_ = v___x_127_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_k_134_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_v_135_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_l_136_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v_l_153_);
v___x_179_ = v_reuseFailAlloc_183_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_nat_add(v___x_131_, v_size_132_);
if (lean_obj_tag(v_r_154_) == 0)
{
lean_object* v_size_181_; 
v_size_181_ = lean_ctor_get(v_r_154_, 0);
lean_inc(v_size_181_);
v___y_164_ = v___x_180_;
v___y_165_ = v___x_179_;
v___y_166_ = v_size_181_;
goto v___jp_163_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___y_164_ = v___x_180_;
v___y_165_ = v___x_179_;
v___y_166_ = v___x_182_;
goto v___jp_163_;
}
}
}
}
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
lean_del_object(v___x_127_);
v___x_192_ = lean_nat_add(v___x_131_, v_size_133_);
lean_dec(v_size_133_);
v___x_193_ = lean_nat_add(v___x_192_, v_size_132_);
lean_dec(v___x_192_);
v___x_194_ = lean_nat_add(v___x_131_, v_size_132_);
v___x_195_ = lean_nat_add(v___x_194_, v_size_150_);
lean_dec(v___x_194_);
lean_inc_ref(v_r_125_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 4, v_r_125_);
lean_ctor_set(v___x_147_, 3, v_r_137_);
lean_ctor_set(v___x_147_, 2, v_v_123_);
lean_ctor_set(v___x_147_, 1, v_k_122_);
lean_ctor_set(v___x_147_, 0, v___x_195_);
v___x_197_ = v___x_147_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_210_, 3, v_r_137_);
lean_ctor_set(v_reuseFailAlloc_210_, 4, v_r_125_);
v___x_197_ = v_reuseFailAlloc_210_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_isSharedCheck_204_ = !lean_is_exclusive(v_r_125_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; lean_object* v_unused_206_; lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_205_ = lean_ctor_get(v_r_125_, 4);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_r_125_, 3);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_r_125_, 2);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_r_125_, 1);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_r_125_, 0);
lean_dec(v_unused_209_);
v___x_199_ = v_r_125_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_r_125_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 4, v___x_197_);
lean_ctor_set(v___x_199_, 3, v_l_136_);
lean_ctor_set(v___x_199_, 2, v_v_135_);
lean_ctor_set(v___x_199_, 1, v_k_134_);
lean_ctor_set(v___x_199_, 0, v___x_193_);
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_134_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_135_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_l_136_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v___x_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_217_; 
v_l_217_ = lean_ctor_get(v_impl_130_, 3);
lean_inc(v_l_217_);
if (lean_obj_tag(v_l_217_) == 0)
{
lean_object* v_r_218_; lean_object* v_k_219_; lean_object* v_v_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_231_; 
v_r_218_ = lean_ctor_get(v_impl_130_, 4);
v_k_219_ = lean_ctor_get(v_impl_130_, 1);
v_v_220_ = lean_ctor_get(v_impl_130_, 2);
v_isSharedCheck_231_ = !lean_is_exclusive(v_impl_130_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; 
v_unused_232_ = lean_ctor_get(v_impl_130_, 3);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_impl_130_, 0);
lean_dec(v_unused_233_);
v___x_222_ = v_impl_130_;
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_r_218_);
lean_inc(v_v_220_);
lean_inc(v_k_219_);
lean_dec(v_impl_130_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_231_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_218_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 3, v_r_218_);
lean_ctor_set(v___x_222_, 2, v_v_123_);
lean_ctor_set(v___x_222_, 1, v_k_122_);
lean_ctor_set(v___x_222_, 0, v___x_131_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_r_218_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_r_218_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___x_226_);
lean_ctor_set(v___x_127_, 3, v_l_217_);
lean_ctor_set(v___x_127_, 2, v_v_220_);
lean_ctor_set(v___x_127_, 1, v_k_219_);
lean_ctor_set(v___x_127_, 0, v___x_224_);
v___x_228_ = v___x_127_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_k_219_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_v_220_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_l_217_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_r_234_; 
v_r_234_ = lean_ctor_get(v_impl_130_, 4);
lean_inc(v_r_234_);
if (lean_obj_tag(v_r_234_) == 0)
{
lean_object* v_k_235_; lean_object* v_v_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_259_; 
v_k_235_ = lean_ctor_get(v_impl_130_, 1);
v_v_236_ = lean_ctor_get(v_impl_130_, 2);
v_isSharedCheck_259_ = !lean_is_exclusive(v_impl_130_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_260_ = lean_ctor_get(v_impl_130_, 4);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_impl_130_, 3);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_impl_130_, 0);
lean_dec(v_unused_262_);
v___x_238_ = v_impl_130_;
v_isShared_239_ = v_isSharedCheck_259_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_v_236_);
lean_inc(v_k_235_);
lean_dec(v_impl_130_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_259_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_255_; 
v_k_240_ = lean_ctor_get(v_r_234_, 1);
v_v_241_ = lean_ctor_get(v_r_234_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_r_234_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_256_ = lean_ctor_get(v_r_234_, 4);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_r_234_, 3);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_r_234_, 0);
lean_dec(v_unused_258_);
v___x_243_ = v_r_234_;
v_isShared_244_ = v_isSharedCheck_255_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_v_241_);
lean_inc(v_k_240_);
lean_dec(v_r_234_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_255_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(3u);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 4, v_l_217_);
lean_ctor_set(v___x_243_, 3, v_l_217_);
lean_ctor_set(v___x_243_, 2, v_v_236_);
lean_ctor_set(v___x_243_, 1, v_k_235_);
lean_ctor_set(v___x_243_, 0, v___x_131_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_235_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_236_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_l_217_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_l_217_);
v___x_247_ = v_reuseFailAlloc_254_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 4, v_l_217_);
lean_ctor_set(v___x_238_, 2, v_v_123_);
lean_ctor_set(v___x_238_, 1, v_k_122_);
lean_ctor_set(v___x_238_, 0, v___x_131_);
v___x_249_ = v___x_238_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_l_217_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_l_217_);
v___x_249_ = v_reuseFailAlloc_253_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_251_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___x_249_);
lean_ctor_set(v___x_127_, 3, v___x_247_);
lean_ctor_set(v___x_127_, 2, v_v_241_);
lean_ctor_set(v___x_127_, 1, v_k_240_);
lean_ctor_set(v___x_127_, 0, v___x_245_);
v___x_251_ = v___x_127_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_241_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(2u);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v_r_234_);
lean_ctor_set(v___x_127_, 3, v_impl_130_);
lean_ctor_set(v___x_127_, 0, v___x_263_);
v___x_265_ = v___x_127_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_266_, 3, v_impl_130_);
lean_ctor_set(v_reuseFailAlloc_266_, 4, v_r_234_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
case 1:
{
lean_object* v___x_268_; 
lean_dec(v_v_123_);
lean_dec(v_k_122_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 2, v_v_119_);
lean_ctor_set(v___x_127_, 1, v_k_118_);
v___x_268_ = v___x_127_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_121_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_k_118_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_v_119_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_l_124_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_r_125_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
default: 
{
lean_object* v_impl_270_; lean_object* v___x_271_; 
lean_dec(v_size_121_);
v_impl_270_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_118_, v_v_119_, v_r_125_);
v___x_271_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_124_) == 0)
{
lean_object* v_size_272_; lean_object* v_size_273_; lean_object* v_k_274_; lean_object* v_v_275_; lean_object* v_l_276_; lean_object* v_r_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_size_272_ = lean_ctor_get(v_l_124_, 0);
v_size_273_ = lean_ctor_get(v_impl_270_, 0);
lean_inc(v_size_273_);
v_k_274_ = lean_ctor_get(v_impl_270_, 1);
lean_inc(v_k_274_);
v_v_275_ = lean_ctor_get(v_impl_270_, 2);
lean_inc(v_v_275_);
v_l_276_ = lean_ctor_get(v_impl_270_, 3);
lean_inc(v_l_276_);
v_r_277_ = lean_ctor_get(v_impl_270_, 4);
lean_inc(v_r_277_);
v___x_278_ = lean_unsigned_to_nat(3u);
v___x_279_ = lean_nat_mul(v___x_278_, v_size_272_);
v___x_280_ = lean_nat_dec_lt(v___x_279_, v_size_273_);
lean_dec(v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec(v_r_277_);
lean_dec(v_l_276_);
lean_dec(v_v_275_);
lean_dec(v_k_274_);
v___x_281_ = lean_nat_add(v___x_271_, v_size_272_);
v___x_282_ = lean_nat_add(v___x_281_, v_size_273_);
lean_dec(v_size_273_);
lean_dec(v___x_281_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v_impl_270_);
lean_ctor_set(v___x_127_, 0, v___x_282_);
v___x_284_ = v___x_127_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_l_124_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_impl_270_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
else
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_349_; 
v_isSharedCheck_349_ = !lean_is_exclusive(v_impl_270_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; 
v_unused_350_ = lean_ctor_get(v_impl_270_, 4);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_impl_270_, 3);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_impl_270_, 2);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_impl_270_, 1);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_impl_270_, 0);
lean_dec(v_unused_354_);
v___x_287_ = v_impl_270_;
v_isShared_288_ = v_isSharedCheck_349_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_impl_270_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_349_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_size_289_; lean_object* v_k_290_; lean_object* v_v_291_; lean_object* v_l_292_; lean_object* v_r_293_; lean_object* v_size_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_size_289_ = lean_ctor_get(v_l_276_, 0);
v_k_290_ = lean_ctor_get(v_l_276_, 1);
v_v_291_ = lean_ctor_get(v_l_276_, 2);
v_l_292_ = lean_ctor_get(v_l_276_, 3);
v_r_293_ = lean_ctor_get(v_l_276_, 4);
v_size_294_ = lean_ctor_get(v_r_277_, 0);
v___x_295_ = lean_unsigned_to_nat(2u);
v___x_296_ = lean_nat_mul(v___x_295_, v_size_294_);
v___x_297_ = lean_nat_dec_lt(v_size_289_, v___x_296_);
lean_dec(v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_325_; 
lean_inc(v_r_293_);
lean_inc(v_l_292_);
lean_inc(v_v_291_);
lean_inc(v_k_290_);
v_isSharedCheck_325_ = !lean_is_exclusive(v_l_276_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; 
v_unused_326_ = lean_ctor_get(v_l_276_, 4);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_l_276_, 3);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_l_276_, 2);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_276_, 1);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_276_, 0);
lean_dec(v_unused_330_);
v___x_299_ = v_l_276_;
v_isShared_300_ = v_isSharedCheck_325_;
goto v_resetjp_298_;
}
else
{
lean_dec(v_l_276_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_325_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_315_; 
v___x_301_ = lean_nat_add(v___x_271_, v_size_272_);
v___x_302_ = lean_nat_add(v___x_301_, v_size_273_);
lean_dec(v_size_273_);
if (lean_obj_tag(v_l_292_) == 0)
{
lean_object* v_size_323_; 
v_size_323_ = lean_ctor_get(v_l_292_, 0);
lean_inc(v_size_323_);
v___y_315_ = v_size_323_;
goto v___jp_314_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___y_315_ = v___x_324_;
goto v___jp_314_;
}
v___jp_303_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = lean_nat_add(v___y_304_, v___y_306_);
lean_dec(v___y_306_);
lean_dec(v___y_304_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 4, v_r_277_);
lean_ctor_set(v___x_299_, 3, v_r_293_);
lean_ctor_set(v___x_299_, 2, v_v_275_);
lean_ctor_set(v___x_299_, 1, v_k_274_);
lean_ctor_set(v___x_299_, 0, v___x_307_);
v___x_309_ = v___x_299_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_k_274_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_v_275_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_r_293_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_r_277_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 4, v___x_309_);
lean_ctor_set(v___x_287_, 3, v___y_305_);
lean_ctor_set(v___x_287_, 2, v_v_291_);
lean_ctor_set(v___x_287_, 1, v_k_290_);
lean_ctor_set(v___x_287_, 0, v___x_302_);
v___x_311_ = v___x_287_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_290_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_291_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v___y_305_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
v___jp_314_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_nat_add(v___x_301_, v___y_315_);
lean_dec(v___y_315_);
lean_dec(v___x_301_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v_l_292_);
lean_ctor_set(v___x_127_, 0, v___x_316_);
v___x_318_ = v___x_127_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_l_124_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v_l_292_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = lean_nat_add(v___x_271_, v_size_294_);
if (lean_obj_tag(v_r_293_) == 0)
{
lean_object* v_size_320_; 
v_size_320_ = lean_ctor_get(v_r_293_, 0);
lean_inc(v_size_320_);
v___y_304_ = v___x_319_;
v___y_305_ = v___x_318_;
v___y_306_ = v_size_320_;
goto v___jp_303_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___y_304_ = v___x_319_;
v___y_305_ = v___x_318_;
v___y_306_ = v___x_321_;
goto v___jp_303_;
}
}
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
lean_del_object(v___x_127_);
v___x_331_ = lean_nat_add(v___x_271_, v_size_272_);
v___x_332_ = lean_nat_add(v___x_331_, v_size_273_);
lean_dec(v_size_273_);
v___x_333_ = lean_nat_add(v___x_331_, v_size_289_);
lean_dec(v___x_331_);
lean_inc_ref(v_l_124_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 4, v_l_276_);
lean_ctor_set(v___x_287_, 3, v_l_124_);
lean_ctor_set(v___x_287_, 2, v_v_123_);
lean_ctor_set(v___x_287_, 1, v_k_122_);
lean_ctor_set(v___x_287_, 0, v___x_333_);
v___x_335_ = v___x_287_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_l_124_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_l_276_);
v___x_335_ = v_reuseFailAlloc_348_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_isSharedCheck_342_ = !lean_is_exclusive(v_l_124_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_343_ = lean_ctor_get(v_l_124_, 4);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_l_124_, 3);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_l_124_, 2);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_l_124_, 1);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_l_124_, 0);
lean_dec(v_unused_347_);
v___x_337_ = v_l_124_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_l_124_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 4, v_r_277_);
lean_ctor_set(v___x_337_, 3, v___x_335_);
lean_ctor_set(v___x_337_, 2, v_v_275_);
lean_ctor_set(v___x_337_, 1, v_k_274_);
lean_ctor_set(v___x_337_, 0, v___x_332_);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_274_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_275_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_r_277_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_355_; 
v_l_355_ = lean_ctor_get(v_impl_270_, 3);
lean_inc(v_l_355_);
if (lean_obj_tag(v_l_355_) == 0)
{
lean_object* v_r_356_; lean_object* v_k_357_; lean_object* v_v_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_381_; 
v_r_356_ = lean_ctor_get(v_impl_270_, 4);
v_k_357_ = lean_ctor_get(v_impl_270_, 1);
v_v_358_ = lean_ctor_get(v_impl_270_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_impl_270_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_382_ = lean_ctor_get(v_impl_270_, 3);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_impl_270_, 0);
lean_dec(v_unused_383_);
v___x_360_ = v_impl_270_;
v_isShared_361_ = v_isSharedCheck_381_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_r_356_);
lean_inc(v_v_358_);
lean_inc(v_k_357_);
lean_dec(v_impl_270_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_381_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_k_362_; lean_object* v_v_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_377_; 
v_k_362_ = lean_ctor_get(v_l_355_, 1);
v_v_363_ = lean_ctor_get(v_l_355_, 2);
v_isSharedCheck_377_ = !lean_is_exclusive(v_l_355_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_378_ = lean_ctor_get(v_l_355_, 4);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_l_355_, 3);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_l_355_, 0);
lean_dec(v_unused_380_);
v___x_365_ = v_l_355_;
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_v_363_);
lean_inc(v_k_362_);
lean_dec(v_l_355_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_356_, 2);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 4, v_r_356_);
lean_ctor_set(v___x_365_, 3, v_r_356_);
lean_ctor_set(v___x_365_, 2, v_v_123_);
lean_ctor_set(v___x_365_, 1, v_k_122_);
lean_ctor_set(v___x_365_, 0, v___x_271_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_r_356_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_r_356_);
v___x_369_ = v_reuseFailAlloc_376_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
lean_inc(v_r_356_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 3, v_r_356_);
lean_ctor_set(v___x_360_, 0, v___x_271_);
v___x_371_ = v___x_360_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_357_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_358_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_r_356_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_r_356_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_373_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v___x_371_);
lean_ctor_set(v___x_127_, 3, v___x_369_);
lean_ctor_set(v___x_127_, 2, v_v_363_);
lean_ctor_set(v___x_127_, 1, v_k_362_);
lean_ctor_set(v___x_127_, 0, v___x_367_);
v___x_373_ = v___x_127_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
else
{
lean_object* v_r_384_; 
v_r_384_ = lean_ctor_get(v_impl_270_, 4);
lean_inc(v_r_384_);
if (lean_obj_tag(v_r_384_) == 0)
{
lean_object* v_k_385_; lean_object* v_v_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_397_; 
v_k_385_ = lean_ctor_get(v_impl_270_, 1);
v_v_386_ = lean_ctor_get(v_impl_270_, 2);
v_isSharedCheck_397_ = !lean_is_exclusive(v_impl_270_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_398_ = lean_ctor_get(v_impl_270_, 4);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_impl_270_, 3);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_impl_270_, 0);
lean_dec(v_unused_400_);
v___x_388_ = v_impl_270_;
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_v_386_);
lean_inc(v_k_385_);
lean_dec(v_impl_270_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_unsigned_to_nat(3u);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v_l_355_);
lean_ctor_set(v___x_388_, 2, v_v_123_);
lean_ctor_set(v___x_388_, 1, v_k_122_);
lean_ctor_set(v___x_388_, 0, v___x_271_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_l_355_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_l_355_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v_r_384_);
lean_ctor_set(v___x_127_, 3, v___x_392_);
lean_ctor_set(v___x_127_, 2, v_v_386_);
lean_ctor_set(v___x_127_, 1, v_k_385_);
lean_ctor_set(v___x_127_, 0, v___x_390_);
v___x_394_ = v___x_127_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_385_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_r_384_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_unsigned_to_nat(2u);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 4, v_impl_270_);
lean_ctor_set(v___x_127_, 3, v_r_384_);
lean_ctor_set(v___x_127_, 0, v___x_401_);
v___x_403_ = v___x_127_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_k_122_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_v_123_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_r_384_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_impl_270_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
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
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_k_118_);
lean_ctor_set(v___x_407_, 2, v_v_119_);
lean_ctor_set(v___x_407_, 3, v_t_120_);
lean_ctor_set(v___x_407_, 4, v_t_120_);
return v___x_407_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object* v_k_408_, lean_object* v_t_409_){
_start:
{
if (lean_obj_tag(v_t_409_) == 0)
{
lean_object* v_k_410_; lean_object* v_l_411_; lean_object* v_r_412_; uint8_t v___x_413_; 
v_k_410_ = lean_ctor_get(v_t_409_, 1);
v_l_411_ = lean_ctor_get(v_t_409_, 3);
v_r_412_ = lean_ctor_get(v_t_409_, 4);
v___x_413_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_408_, v_k_410_);
switch(v___x_413_)
{
case 0:
{
v_t_409_ = v_l_411_;
goto _start;
}
case 1:
{
uint8_t v___x_415_; 
v___x_415_ = 1;
return v___x_415_;
}
default: 
{
v_t_409_ = v_r_412_;
goto _start;
}
}
}
else
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object* v_k_418_, lean_object* v_t_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_418_, v_t_419_);
lean_dec(v_t_419_);
lean_dec(v_k_418_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* v_x_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
switch(lean_obj_tag(v_x_422_))
{
case 0:
{
lean_object* v_e_425_; lean_object* v_b_426_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; lean_object* v_f_440_; lean_object* v___y_441_; lean_object* v___y_442_; 
v_e_425_ = lean_ctor_get(v_x_422_, 2);
lean_inc_ref(v_e_425_);
v_b_426_ = lean_ctor_get(v_x_422_, 3);
lean_inc(v_b_426_);
lean_dec_ref_known(v_x_422_, 4);
switch(lean_obj_tag(v_e_425_))
{
case 6:
{
lean_object* v_c_450_; 
v_c_450_ = lean_ctor_get(v_e_425_, 0);
lean_inc(v_c_450_);
lean_dec_ref_known(v_e_425_, 2);
v_f_440_ = v_c_450_;
v___y_441_ = v_a_423_;
v___y_442_ = v_a_424_;
goto v___jp_439_;
}
case 7:
{
lean_object* v_c_451_; 
v_c_451_ = lean_ctor_get(v_e_425_, 0);
lean_inc(v_c_451_);
lean_dec_ref_known(v_e_425_, 2);
v_f_440_ = v_c_451_;
v___y_441_ = v_a_423_;
v___y_442_ = v_a_424_;
goto v___jp_439_;
}
default: 
{
lean_dec_ref(v_e_425_);
v_x_422_ = v_b_426_;
goto _start;
}
}
v___jp_427_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_unbox(v_fst_431_);
lean_dec(v_fst_431_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_array_push(v___y_430_, v___y_428_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_snd_432_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v_x_422_ = v_b_426_;
v_a_423_ = v___y_429_;
v_a_424_ = v___x_435_;
goto _start;
}
else
{
lean_object* v___x_437_; 
lean_dec(v___y_428_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_snd_432_);
lean_ctor_set(v___x_437_, 1, v___y_430_);
v_x_422_ = v_b_426_;
v_a_423_ = v___y_429_;
v_a_424_ = v___x_437_;
goto _start;
}
}
v___jp_439_:
{
lean_object* v_set_443_; lean_object* v_order_444_; uint8_t v___x_445_; 
v_set_443_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_set_443_);
v_order_444_ = lean_ctor_get(v___y_442_, 1);
lean_inc_ref(v_order_444_);
lean_dec_ref(v___y_442_);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_f_440_, v_set_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
lean_inc(v_f_440_);
v___x_447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_f_440_, v___x_446_, v_set_443_);
v___x_448_ = lean_box(v___x_445_);
v___y_428_ = v_f_440_;
v___y_429_ = v___y_441_;
v___y_430_ = v_order_444_;
v_fst_431_ = v___x_448_;
v_snd_432_ = v___x_447_;
goto v___jp_427_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_box(v___x_445_);
v___y_428_ = v_f_440_;
v___y_429_ = v___y_441_;
v___y_430_ = v_order_444_;
v_fst_431_ = v___x_449_;
v_snd_432_ = v_set_443_;
goto v___jp_427_;
}
}
}
case 1:
{
lean_object* v_v_453_; lean_object* v_b_454_; lean_object* v___x_455_; lean_object* v_snd_456_; 
v_v_453_ = lean_ctor_get(v_x_422_, 2);
lean_inc(v_v_453_);
v_b_454_ = lean_ctor_get(v_x_422_, 3);
lean_inc(v_b_454_);
lean_dec_ref_known(v_x_422_, 4);
v___x_455_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_453_, v_a_423_, v_a_424_);
v_snd_456_ = lean_ctor_get(v___x_455_, 1);
lean_inc(v_snd_456_);
lean_dec_ref(v___x_455_);
v_x_422_ = v_b_454_;
v_a_424_ = v_snd_456_;
goto _start;
}
case 9:
{
lean_object* v_cs_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_cs_458_ = lean_ctor_get(v_x_422_, 3);
lean_inc_ref(v_cs_458_);
lean_dec_ref_known(v_x_422_, 4);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_array_get_size(v_cs_458_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_nat_dec_lt(v___x_459_, v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec_ref(v_cs_458_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v_a_424_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_le(v___x_460_, v___x_460_);
if (v___x_464_ == 0)
{
if (v___x_462_ == 0)
{
lean_object* v___x_465_; 
lean_dec_ref(v_cs_458_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_461_);
lean_ctor_set(v___x_465_, 1, v_a_424_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_460_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_458_, v___x_466_, v___x_467_, v___x_461_, v_a_423_, v_a_424_);
lean_dec_ref(v_cs_458_);
return v___x_468_;
}
}
else
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((size_t)0ULL);
v___x_470_ = lean_usize_of_nat(v___x_460_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_458_, v___x_469_, v___x_470_, v___x_461_, v_a_423_, v_a_424_);
lean_dec_ref(v_cs_458_);
return v___x_471_;
}
}
}
default: 
{
uint8_t v___x_472_; 
v___x_472_ = l_Lean_IR_FnBody_isTerminal(v_x_422_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_IR_FnBody_body(v_x_422_);
lean_dec(v_x_422_);
v_x_422_ = v___x_473_;
goto _start;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v_x_422_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_a_424_);
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object* v_as_477_, size_t v_i_478_, size_t v_stop_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_eq(v_i_478_, v_stop_479_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_fst_487_; lean_object* v_snd_488_; size_t v___x_489_; size_t v___x_490_; 
v___x_484_ = lean_array_uget_borrowed(v_as_477_, v_i_478_);
v___x_485_ = l_Lean_IR_Alt_body(v___x_484_);
v___x_486_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v___x_485_, v___y_481_, v___y_482_);
v_fst_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_fst_487_);
v_snd_488_ = lean_ctor_get(v___x_486_, 1);
lean_inc(v_snd_488_);
lean_dec_ref(v___x_486_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_478_, v___x_489_);
v_i_478_ = v___x_490_;
v_b_480_ = v_fst_487_;
v___y_482_ = v_snd_488_;
goto _start;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_b_480_);
lean_ctor_set(v___x_492_, 1, v___y_482_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object* v_as_493_, lean_object* v_i_494_, lean_object* v_stop_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
size_t v_i_boxed_499_; size_t v_stop_boxed_500_; lean_object* v_res_501_; 
v_i_boxed_499_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_stop_boxed_500_ = lean_unbox_usize(v_stop_495_);
lean_dec(v_stop_495_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_493_, v_i_boxed_499_, v_stop_boxed_500_, v_b_496_, v___y_497_, v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec_ref(v_as_493_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* v_x_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_502_, v_a_503_, v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_505_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object* v_00_u03b2_506_, lean_object* v_k_507_, lean_object* v_t_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_507_, v_t_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_510_, lean_object* v_k_511_, lean_object* v_t_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_510_, v_k_511_, v_t_512_);
lean_dec(v_t_512_);
lean_dec(v_k_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object* v_00_u03b2_515_, lean_object* v_k_516_, lean_object* v_v_517_, lean_object* v_t_518_, lean_object* v_hl_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_516_, v_v_517_, v_t_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* v_fn_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_524_; 
lean_inc_ref(v_a_522_);
v___x_524_ = lean_get_init_fn_name_for(v_a_522_, v_fn_521_);
if (lean_obj_tag(v___x_524_) == 1)
{
lean_object* v_val_525_; lean_object* v_set_526_; lean_object* v_order_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_549_; 
v_val_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v___x_524_, 1);
v_set_526_ = lean_ctor_get(v_a_523_, 0);
v_order_527_ = lean_ctor_get(v_a_523_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_523_);
if (v_isSharedCheck_549_ == 0)
{
v___x_529_ = v_a_523_;
v_isShared_530_ = v_isSharedCheck_549_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_order_527_);
lean_inc(v_set_526_);
lean_dec(v_a_523_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_549_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v_fst_533_; lean_object* v_snd_534_; uint8_t v___x_545_; 
v___x_531_ = lean_box(0);
v___x_545_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_525_, v_set_526_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_inc(v_val_525_);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_525_, v___x_531_, v_set_526_);
v___x_547_ = lean_box(v___x_545_);
v_fst_533_ = v___x_547_;
v_snd_534_ = v___x_546_;
goto v___jp_532_;
}
else
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(v___x_545_);
v_fst_533_ = v___x_548_;
v_snd_534_ = v_set_526_;
goto v___jp_532_;
}
v___jp_532_:
{
uint8_t v___x_535_; 
v___x_535_ = lean_unbox(v_fst_533_);
lean_dec(v_fst_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_push(v_order_527_, v_val_525_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v___x_536_);
lean_ctor_set(v___x_529_, 0, v_snd_534_);
v___x_538_ = v___x_529_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_snd_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_540_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_531_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
return v___x_539_;
}
}
else
{
lean_object* v___x_542_; 
lean_dec(v_val_525_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_snd_534_);
v___x_542_ = v___x_529_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_snd_534_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_order_527_);
v___x_542_ = v_reuseFailAlloc_544_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_531_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
return v___x_543_;
}
}
}
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_524_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_523_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object* v_fn_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_552_, v_a_553_, v_a_554_);
lean_dec_ref(v_a_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
if (lean_obj_tag(v_x_556_) == 0)
{
lean_object* v_f_559_; lean_object* v_body_560_; lean_object* v___x_561_; lean_object* v_snd_562_; lean_object* v___x_563_; 
v_f_559_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_f_559_);
v_body_560_ = lean_ctor_get(v_x_556_, 3);
lean_inc(v_body_560_);
lean_dec_ref_known(v_x_556_, 5);
v___x_561_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_559_, v_a_557_, v_a_558_);
v_snd_562_ = lean_ctor_get(v___x_561_, 1);
lean_inc(v_snd_562_);
lean_dec_ref(v___x_561_);
v___x_563_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_560_, v_a_557_, v_snd_562_);
return v___x_563_;
}
else
{
lean_object* v_f_564_; lean_object* v___x_565_; 
v_f_564_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_f_564_);
lean_dec_ref_known(v_x_556_, 4);
v___x_565_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_564_, v_a_557_, v_a_558_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object* v_x_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_566_, v_a_567_, v_a_568_);
lean_dec_ref(v_a_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
if (lean_obj_tag(v_as_570_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___y_572_);
return v___x_574_;
}
else
{
lean_object* v_head_575_; lean_object* v_tail_576_; lean_object* v___x_577_; lean_object* v_snd_578_; lean_object* v_set_579_; lean_object* v_order_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_603_; 
v_head_575_ = lean_ctor_get(v_as_570_, 0);
lean_inc_n(v_head_575_, 2);
v_tail_576_ = lean_ctor_get(v_as_570_, 1);
lean_inc(v_tail_576_);
lean_dec_ref_known(v_as_570_, 2);
v___x_577_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_575_, v___y_571_, v___y_572_);
v_snd_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_snd_578_);
lean_dec_ref(v___x_577_);
v_set_579_ = lean_ctor_get(v_snd_578_, 0);
v_order_580_ = lean_ctor_get(v_snd_578_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_snd_578_);
if (v_isSharedCheck_603_ == 0)
{
v___x_582_ = v_snd_578_;
v_isShared_583_ = v_isSharedCheck_603_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_order_580_);
lean_inc(v_set_579_);
lean_dec(v_snd_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_603_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v_fst_586_; lean_object* v_snd_587_; uint8_t v___x_598_; 
v___x_584_ = l_Lean_IR_Decl_name(v_head_575_);
lean_dec(v_head_575_);
v___x_598_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_584_, v_set_579_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
lean_inc(v___x_584_);
v___x_600_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_584_, v___x_599_, v_set_579_);
v___x_601_ = lean_box(v___x_598_);
v_fst_586_ = v___x_601_;
v_snd_587_ = v___x_600_;
goto v___jp_585_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(v___x_598_);
v_fst_586_ = v___x_602_;
v_snd_587_ = v_set_579_;
goto v___jp_585_;
}
v___jp_585_:
{
uint8_t v___x_588_; 
v___x_588_ = lean_unbox(v_fst_586_);
lean_dec(v_fst_586_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_array_push(v_order_580_, v___x_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v___x_589_);
lean_ctor_set(v___x_582_, 0, v_snd_587_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_snd_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_593_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
v_as_570_ = v_tail_576_;
v___y_572_ = v___x_591_;
goto _start;
}
}
else
{
lean_object* v___x_595_; 
lean_dec(v___x_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_snd_587_);
v___x_595_ = v___x_582_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_snd_587_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_order_580_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v_as_570_ = v_tail_576_;
v___y_572_ = v___x_595_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object* v_as_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_as_604_, v___y_605_, v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_608_, v_a_609_, v_a_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object* v_decls_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_612_, v_a_613_, v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_619_ = l_Lean_NameSet_empty;
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_621_, lean_object* v_decls_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_snd_625_; lean_object* v_order_626_; 
v___x_623_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_624_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_622_, v_env_621_, v___x_623_);
v_snd_625_ = lean_ctor_get(v___x_624_, 1);
lean_inc(v_snd_625_);
lean_dec_ref(v___x_624_);
v_order_626_ = lean_ctor_get(v_snd_625_, 1);
lean_inc_ref(v_order_626_);
lean_dec(v_snd_625_);
return v_order_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object* v_env_627_, lean_object* v_decls_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_IR_collectUsedDecls(v_env_627_, v_decls_628_);
lean_dec_ref(v_env_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_632_, lean_object* v_t_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_fst_635_; lean_object* v_snd_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_646_; 
v_fst_635_ = lean_ctor_get(v_x_634_, 0);
v_snd_636_ = lean_ctor_get(v_x_634_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_646_ == 0)
{
v___x_638_ = v_x_634_;
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snd_636_);
lean_inc(v_fst_635_);
lean_dec(v_x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_640_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_641_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_640_, v___x_641_, v_fst_635_, v_x_632_, v_t_633_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_642_);
v___x_644_ = v___x_638_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_snd_636_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
return v_x_647_;
}
else
{
lean_object* v_key_649_; lean_object* v_value_650_; lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_674_; 
v_key_649_ = lean_ctor_get(v_x_648_, 0);
v_value_650_ = lean_ctor_get(v_x_648_, 1);
v_tail_651_ = lean_ctor_get(v_x_648_, 2);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_674_ == 0)
{
v___x_653_ = v_x_648_;
v_isShared_654_ = v_isSharedCheck_674_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_inc(v_value_650_);
lean_inc(v_key_649_);
lean_dec(v_x_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_674_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v_fold_659_; uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_655_ = lean_array_get_size(v_x_647_);
v___x_656_ = l_Lean_IR_instHashableVarId_hash(v_key_649_);
v___x_657_ = 32ULL;
v___x_658_ = lean_uint64_shift_right(v___x_656_, v___x_657_);
v_fold_659_ = lean_uint64_xor(v___x_656_, v___x_658_);
v___x_660_ = 16ULL;
v___x_661_ = lean_uint64_shift_right(v_fold_659_, v___x_660_);
v___x_662_ = lean_uint64_xor(v_fold_659_, v___x_661_);
v___x_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = lean_usize_of_nat(v___x_655_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_sub(v___x_664_, v___x_665_);
v___x_667_ = lean_usize_land(v___x_663_, v___x_666_);
v___x_668_ = lean_array_uget_borrowed(v_x_647_, v___x_667_);
lean_inc(v___x_668_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 2, v___x_668_);
v___x_670_ = v___x_653_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_key_649_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_value_650_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v___x_668_);
v___x_670_ = v_reuseFailAlloc_673_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_array_uset(v_x_647_, v___x_667_, v___x_670_);
v_x_647_ = v___x_671_;
v_x_648_ = v_tail_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_675_, lean_object* v_source_676_, lean_object* v_target_677_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_array_get_size(v_source_676_);
v___x_679_ = lean_nat_dec_lt(v_i_675_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec_ref(v_source_676_);
lean_dec(v_i_675_);
return v_target_677_;
}
else
{
lean_object* v_es_680_; lean_object* v___x_681_; lean_object* v_source_682_; lean_object* v_target_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_es_680_ = lean_array_fget(v_source_676_, v_i_675_);
v___x_681_ = lean_box(0);
v_source_682_ = lean_array_fset(v_source_676_, v_i_675_, v___x_681_);
v_target_683_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_677_, v_es_680_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_add(v_i_675_, v___x_684_);
lean_dec(v_i_675_);
v_i_675_ = v___x_685_;
v_source_676_ = v_source_682_;
v_target_677_ = v_target_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_687_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_nbuckets_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_688_ = lean_array_get_size(v_data_687_);
v___x_689_ = lean_unsigned_to_nat(2u);
v_nbuckets_690_ = lean_nat_mul(v___x_688_, v___x_689_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_box(0);
v___x_693_ = lean_mk_array(v_nbuckets_690_, v___x_692_);
v___x_694_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_691_, v_data_687_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
else
{
lean_object* v_key_698_; lean_object* v_tail_699_; uint8_t v___x_700_; 
v_key_698_ = lean_ctor_get(v_x_696_, 0);
v_tail_699_ = lean_ctor_get(v_x_696_, 2);
v___x_700_ = l_Lean_IR_instBEqVarId_beq(v_key_698_, v_a_695_);
if (v___x_700_ == 0)
{
v_x_696_ = v_tail_699_;
goto _start;
}
else
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_702_, v_x_703_);
lean_dec(v_x_703_);
lean_dec(v_a_702_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_706_, lean_object* v_b_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_dec(v_b_707_);
lean_dec(v_a_706_);
return v_x_708_;
}
else
{
lean_object* v_key_709_; lean_object* v_value_710_; lean_object* v_tail_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_723_; 
v_key_709_ = lean_ctor_get(v_x_708_, 0);
v_value_710_ = lean_ctor_get(v_x_708_, 1);
v_tail_711_ = lean_ctor_get(v_x_708_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_708_);
if (v_isSharedCheck_723_ == 0)
{
v___x_713_ = v_x_708_;
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_tail_711_);
lean_inc(v_value_710_);
lean_inc(v_key_709_);
lean_dec(v_x_708_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_723_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
uint8_t v___x_715_; 
v___x_715_ = l_Lean_IR_instBEqVarId_beq(v_key_709_, v_a_706_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_706_, v_b_707_, v_tail_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 2, v___x_716_);
v___x_718_ = v___x_713_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_key_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_value_710_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v_value_710_);
lean_dec(v_key_709_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v_b_707_);
lean_ctor_set(v___x_713_, 0, v_a_706_);
v___x_721_ = v___x_713_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_706_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_b_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_tail_711_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_724_, lean_object* v_a_725_, lean_object* v_b_726_){
_start:
{
lean_object* v_size_727_; lean_object* v_buckets_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_771_; 
v_size_727_ = lean_ctor_get(v_m_724_, 0);
v_buckets_728_ = lean_ctor_get(v_m_724_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_m_724_);
if (v_isSharedCheck_771_ == 0)
{
v___x_730_ = v_m_724_;
v_isShared_731_ = v_isSharedCheck_771_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_buckets_728_);
lean_inc(v_size_727_);
lean_dec(v_m_724_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_771_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; uint64_t v___x_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v_fold_736_; uint64_t v___x_737_; uint64_t v___x_738_; uint64_t v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; lean_object* v_bkt_745_; uint8_t v___x_746_; 
v___x_732_ = lean_array_get_size(v_buckets_728_);
v___x_733_ = l_Lean_IR_instHashableVarId_hash(v_a_725_);
v___x_734_ = 32ULL;
v___x_735_ = lean_uint64_shift_right(v___x_733_, v___x_734_);
v_fold_736_ = lean_uint64_xor(v___x_733_, v___x_735_);
v___x_737_ = 16ULL;
v___x_738_ = lean_uint64_shift_right(v_fold_736_, v___x_737_);
v___x_739_ = lean_uint64_xor(v_fold_736_, v___x_738_);
v___x_740_ = lean_uint64_to_usize(v___x_739_);
v___x_741_ = lean_usize_of_nat(v___x_732_);
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_sub(v___x_741_, v___x_742_);
v___x_744_ = lean_usize_land(v___x_740_, v___x_743_);
v_bkt_745_ = lean_array_uget_borrowed(v_buckets_728_, v___x_744_);
v___x_746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_725_, v_bkt_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v_size_x27_748_; lean_object* v___x_749_; lean_object* v_buckets_x27_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_747_ = lean_unsigned_to_nat(1u);
v_size_x27_748_ = lean_nat_add(v_size_727_, v___x_747_);
lean_dec(v_size_727_);
lean_inc(v_bkt_745_);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v_a_725_);
lean_ctor_set(v___x_749_, 1, v_b_726_);
lean_ctor_set(v___x_749_, 2, v_bkt_745_);
v_buckets_x27_750_ = lean_array_uset(v_buckets_728_, v___x_744_, v___x_749_);
v___x_751_ = lean_unsigned_to_nat(4u);
v___x_752_ = lean_nat_mul(v_size_x27_748_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(3u);
v___x_754_ = lean_nat_div(v___x_752_, v___x_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_array_get_size(v_buckets_x27_750_);
v___x_756_ = lean_nat_dec_le(v___x_754_, v___x_755_);
lean_dec(v___x_754_);
if (v___x_756_ == 0)
{
lean_object* v_val_757_; lean_object* v___x_759_; 
v_val_757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_750_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_val_757_);
lean_ctor_set(v___x_730_, 0, v_size_x27_748_);
v___x_759_ = v___x_730_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_size_x27_748_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_val_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v___x_762_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v_buckets_x27_750_);
lean_ctor_set(v___x_730_, 0, v_size_x27_748_);
v___x_762_ = v___x_730_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_size_x27_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_buckets_x27_750_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v___x_764_; lean_object* v_buckets_x27_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
lean_inc(v_bkt_745_);
v___x_764_ = lean_box(0);
v_buckets_x27_765_ = lean_array_uset(v_buckets_728_, v___x_744_, v___x_764_);
v___x_766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_725_, v_b_726_, v_bkt_745_);
v___x_767_ = lean_array_uset(v_buckets_x27_765_, v___x_744_, v___x_766_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_767_);
v___x_769_ = v___x_730_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_size_727_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_772_, size_t v_i_773_, size_t v_stop_774_, lean_object* v_b_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_eq(v_i_773_, v_stop_774_);
if (v___x_776_ == 0)
{
lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_792_; 
v_fst_777_ = lean_ctor_get(v_b_775_, 0);
v_snd_778_ = lean_ctor_get(v_b_775_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_b_775_);
if (v_isSharedCheck_792_ == 0)
{
v___x_780_ = v_b_775_;
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
lean_dec(v_b_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_792_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v_x_783_; lean_object* v_ty_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_782_ = lean_array_uget_borrowed(v_as_772_, v_i_773_);
v_x_783_ = lean_ctor_get(v___x_782_, 0);
v_ty_784_ = lean_ctor_get(v___x_782_, 1);
lean_inc(v_ty_784_);
lean_inc(v_x_783_);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_777_, v_x_783_, v_ty_784_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_785_);
v___x_787_ = v___x_780_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_snd_778_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
size_t v___x_788_; size_t v___x_789_; 
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_773_, v___x_788_);
v_i_773_ = v___x_789_;
v_b_775_ = v___x_787_;
goto _start;
}
}
}
else
{
return v_b_775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_793_, lean_object* v_i_794_, lean_object* v_stop_795_, lean_object* v_b_796_){
_start:
{
size_t v_i_boxed_797_; size_t v_stop_boxed_798_; lean_object* v_res_799_; 
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_stop_boxed_798_ = lean_unbox_usize(v_stop_795_);
lean_dec(v_stop_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_793_, v_i_boxed_797_, v_stop_boxed_798_, v_b_796_);
lean_dec_ref(v_as_793_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_800_, lean_object* v_s_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_array_get_size(v_ps_800_);
v___x_804_ = lean_nat_dec_lt(v___x_802_, v___x_803_);
if (v___x_804_ == 0)
{
return v_s_801_;
}
else
{
uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_le(v___x_803_, v___x_803_);
if (v___x_805_ == 0)
{
if (v___x_804_ == 0)
{
return v_s_801_;
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_803_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_800_, v___x_806_, v___x_807_, v_s_801_);
return v___x_808_;
}
}
else
{
size_t v___x_809_; size_t v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((size_t)0ULL);
v___x_810_ = lean_usize_of_nat(v___x_803_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_800_, v___x_809_, v___x_810_, v_s_801_);
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_812_, lean_object* v_s_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_IR_CollectMaps_collectParams(v_ps_812_, v_s_813_);
lean_dec_ref(v_ps_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_b_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_816_, v_a_817_, v_b_818_);
return v___x_819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_824_, v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_829_, lean_object* v_data_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_b_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_833_, v_b_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_837_, lean_object* v_i_838_, lean_object* v_source_839_, lean_object* v_target_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_838_, v_source_839_, v_target_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_848_, lean_object* v_xs_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_fst_851_ = lean_ctor_get(v_x_850_, 0);
v_snd_852_ = lean_ctor_get(v_x_850_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v_x_850_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_852_);
lean_inc(v_fst_851_);
lean_dec(v_x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_856_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_857_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_856_, v___x_857_, v_snd_852_, v_j_848_, v_xs_849_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_858_);
v___x_860_ = v___x_854_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
uint8_t v___x_865_; 
v___x_865_ = 0;
return v___x_865_;
}
else
{
lean_object* v_key_866_; lean_object* v_tail_867_; uint8_t v___x_868_; 
v_key_866_ = lean_ctor_get(v_x_864_, 0);
v_tail_867_ = lean_ctor_get(v_x_864_, 2);
v___x_868_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_866_, v_a_863_);
if (v___x_868_ == 0)
{
v_x_864_ = v_tail_867_;
goto _start;
}
else
{
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec(v_a_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
return v_x_874_;
}
else
{
lean_object* v_key_876_; lean_object* v_value_877_; lean_object* v_tail_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_901_; 
v_key_876_ = lean_ctor_get(v_x_875_, 0);
v_value_877_ = lean_ctor_get(v_x_875_, 1);
v_tail_878_ = lean_ctor_get(v_x_875_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_875_);
if (v_isSharedCheck_901_ == 0)
{
v___x_880_ = v_x_875_;
v_isShared_881_ = v_isSharedCheck_901_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_tail_878_);
lean_inc(v_value_877_);
lean_inc(v_key_876_);
lean_dec(v_x_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_901_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v_fold_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_882_ = lean_array_get_size(v_x_874_);
v___x_883_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_876_);
v___x_884_ = 32ULL;
v___x_885_ = lean_uint64_shift_right(v___x_883_, v___x_884_);
v_fold_886_ = lean_uint64_xor(v___x_883_, v___x_885_);
v___x_887_ = 16ULL;
v___x_888_ = lean_uint64_shift_right(v_fold_886_, v___x_887_);
v___x_889_ = lean_uint64_xor(v_fold_886_, v___x_888_);
v___x_890_ = lean_uint64_to_usize(v___x_889_);
v___x_891_ = lean_usize_of_nat(v___x_882_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_sub(v___x_891_, v___x_892_);
v___x_894_ = lean_usize_land(v___x_890_, v___x_893_);
v___x_895_ = lean_array_uget_borrowed(v_x_874_, v___x_894_);
lean_inc(v___x_895_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v___x_895_);
v___x_897_ = v___x_880_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_key_876_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_value_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v___x_895_);
v___x_897_ = v_reuseFailAlloc_900_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; 
v___x_898_ = lean_array_uset(v_x_874_, v___x_894_, v___x_897_);
v_x_874_ = v___x_898_;
v_x_875_ = v_tail_878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_902_, lean_object* v_source_903_, lean_object* v_target_904_){
_start:
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = lean_array_get_size(v_source_903_);
v___x_906_ = lean_nat_dec_lt(v_i_902_, v___x_905_);
if (v___x_906_ == 0)
{
lean_dec_ref(v_source_903_);
lean_dec(v_i_902_);
return v_target_904_;
}
else
{
lean_object* v_es_907_; lean_object* v___x_908_; lean_object* v_source_909_; lean_object* v_target_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_es_907_ = lean_array_fget(v_source_903_, v_i_902_);
v___x_908_ = lean_box(0);
v_source_909_ = lean_array_fset(v_source_903_, v_i_902_, v___x_908_);
v_target_910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_904_, v_es_907_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_902_, v___x_911_);
lean_dec(v_i_902_);
v_i_902_ = v___x_912_;
v_source_903_ = v_source_909_;
v_target_904_ = v_target_910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_914_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_nbuckets_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_915_ = lean_array_get_size(v_data_914_);
v___x_916_ = lean_unsigned_to_nat(2u);
v_nbuckets_917_ = lean_nat_mul(v___x_915_, v___x_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_box(0);
v___x_920_ = lean_mk_array(v_nbuckets_917_, v___x_919_);
v___x_921_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_918_, v_data_914_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_922_, lean_object* v_b_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
lean_dec(v_b_923_);
lean_dec(v_a_922_);
return v_x_924_;
}
else
{
lean_object* v_key_925_; lean_object* v_value_926_; lean_object* v_tail_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_939_; 
v_key_925_ = lean_ctor_get(v_x_924_, 0);
v_value_926_ = lean_ctor_get(v_x_924_, 1);
v_tail_927_ = lean_ctor_get(v_x_924_, 2);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_939_ == 0)
{
v___x_929_ = v_x_924_;
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_tail_927_);
lean_inc(v_value_926_);
lean_inc(v_key_925_);
lean_dec(v_x_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_939_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint8_t v___x_931_; 
v___x_931_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_925_, v_a_922_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_922_, v_b_923_, v_tail_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 2, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_key_925_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_value_926_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v___x_937_; 
lean_dec(v_value_926_);
lean_dec(v_key_925_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v_b_923_);
lean_ctor_set(v___x_929_, 0, v_a_922_);
v___x_937_ = v___x_929_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_922_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_b_923_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_tail_927_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_940_, lean_object* v_a_941_, lean_object* v_b_942_){
_start:
{
lean_object* v_size_943_; lean_object* v_buckets_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_987_; 
v_size_943_ = lean_ctor_get(v_m_940_, 0);
v_buckets_944_ = lean_ctor_get(v_m_940_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_m_940_);
if (v_isSharedCheck_987_ == 0)
{
v___x_946_ = v_m_940_;
v_isShared_947_ = v_isSharedCheck_987_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_buckets_944_);
lean_inc(v_size_943_);
lean_dec(v_m_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_987_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; uint64_t v_fold_952_; uint64_t v___x_953_; uint64_t v___x_954_; uint64_t v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; size_t v___x_960_; lean_object* v_bkt_961_; uint8_t v___x_962_; 
v___x_948_ = lean_array_get_size(v_buckets_944_);
v___x_949_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_941_);
v___x_950_ = 32ULL;
v___x_951_ = lean_uint64_shift_right(v___x_949_, v___x_950_);
v_fold_952_ = lean_uint64_xor(v___x_949_, v___x_951_);
v___x_953_ = 16ULL;
v___x_954_ = lean_uint64_shift_right(v_fold_952_, v___x_953_);
v___x_955_ = lean_uint64_xor(v_fold_952_, v___x_954_);
v___x_956_ = lean_uint64_to_usize(v___x_955_);
v___x_957_ = lean_usize_of_nat(v___x_948_);
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_sub(v___x_957_, v___x_958_);
v___x_960_ = lean_usize_land(v___x_956_, v___x_959_);
v_bkt_961_ = lean_array_uget_borrowed(v_buckets_944_, v___x_960_);
v___x_962_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_941_, v_bkt_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v_size_x27_964_; lean_object* v___x_965_; lean_object* v_buckets_x27_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_963_ = lean_unsigned_to_nat(1u);
v_size_x27_964_ = lean_nat_add(v_size_943_, v___x_963_);
lean_dec(v_size_943_);
lean_inc(v_bkt_961_);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v_a_941_);
lean_ctor_set(v___x_965_, 1, v_b_942_);
lean_ctor_set(v___x_965_, 2, v_bkt_961_);
v_buckets_x27_966_ = lean_array_uset(v_buckets_944_, v___x_960_, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(4u);
v___x_968_ = lean_nat_mul(v_size_x27_964_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(3u);
v___x_970_ = lean_nat_div(v___x_968_, v___x_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_array_get_size(v_buckets_x27_966_);
v___x_972_ = lean_nat_dec_le(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
if (v___x_972_ == 0)
{
lean_object* v_val_973_; lean_object* v___x_975_; 
v_val_973_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_966_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v_val_973_);
lean_ctor_set(v___x_946_, 0, v_size_x27_964_);
v___x_975_ = v___x_946_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_size_x27_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_val_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v___x_978_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v_buckets_x27_966_);
lean_ctor_set(v___x_946_, 0, v_size_x27_964_);
v___x_978_ = v___x_946_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_size_x27_964_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_buckets_x27_966_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v___x_980_; lean_object* v_buckets_x27_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
lean_inc(v_bkt_961_);
v___x_980_ = lean_box(0);
v_buckets_x27_981_ = lean_array_uset(v_buckets_944_, v___x_960_, v___x_980_);
v___x_982_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_941_, v_b_942_, v_bkt_961_);
v___x_983_ = lean_array_uset(v_buckets_x27_981_, v___x_960_, v___x_982_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_983_);
v___x_985_ = v___x_946_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_size_943_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_988_, lean_object* v_a_989_){
_start:
{
switch(lean_obj_tag(v_x_988_))
{
case 0:
{
lean_object* v_x_990_; lean_object* v_ty_991_; lean_object* v_b_992_; lean_object* v___x_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v_x_990_ = lean_ctor_get(v_x_988_, 0);
lean_inc(v_x_990_);
v_ty_991_ = lean_ctor_get(v_x_988_, 1);
lean_inc(v_ty_991_);
v_b_992_ = lean_ctor_get(v_x_988_, 3);
lean_inc(v_b_992_);
lean_dec_ref_known(v_x_988_, 4);
v___x_993_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_992_, v_a_989_);
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
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_994_, v_x_990_, v_ty_991_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_snd_995_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
case 1:
{
lean_object* v_j_1004_; lean_object* v_xs_1005_; lean_object* v_v_1006_; lean_object* v_b_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_j_1004_ = lean_ctor_get(v_x_988_, 0);
lean_inc(v_j_1004_);
v_xs_1005_ = lean_ctor_get(v_x_988_, 1);
lean_inc_ref(v_xs_1005_);
v_v_1006_ = lean_ctor_get(v_x_988_, 2);
lean_inc(v_v_1006_);
v_b_1007_ = lean_ctor_get(v_x_988_, 3);
lean_inc(v_b_1007_);
lean_dec_ref_known(v_x_988_, 4);
v___x_1008_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1007_, v_a_989_);
v___x_1009_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_1006_, v___x_1008_);
v___x_1010_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1005_, v___x_1009_);
v_fst_1011_ = lean_ctor_get(v___x_1010_, 0);
v_snd_1012_ = lean_ctor_get(v___x_1010_, 1);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_1010_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snd_1012_);
lean_inc(v_fst_1011_);
lean_dec(v___x_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_1012_, v_j_1004_, v_xs_1005_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 1, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_fst_1011_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
case 9:
{
lean_object* v_cs_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_cs_1021_ = lean_ctor_get(v_x_988_, 3);
lean_inc_ref(v_cs_1021_);
lean_dec_ref_known(v_x_988_, 4);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_array_get_size(v_cs_1021_);
v___x_1024_ = lean_nat_dec_lt(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec_ref(v_cs_1021_);
return v_a_989_;
}
else
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_nat_dec_le(v___x_1023_, v___x_1023_);
if (v___x_1025_ == 0)
{
if (v___x_1024_ == 0)
{
lean_dec_ref(v_cs_1021_);
return v_a_989_;
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1023_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1021_, v___x_1026_, v___x_1027_, v_a_989_);
lean_dec_ref(v_cs_1021_);
return v___x_1028_;
}
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = lean_usize_of_nat(v___x_1023_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1021_, v___x_1029_, v___x_1030_, v_a_989_);
lean_dec_ref(v_cs_1021_);
return v___x_1031_;
}
}
}
default: 
{
uint8_t v___x_1032_; 
v___x_1032_ = l_Lean_IR_FnBody_isTerminal(v_x_988_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_IR_FnBody_body(v_x_988_);
lean_dec(v_x_988_);
v_x_988_ = v___x_1033_;
goto _start;
}
else
{
lean_dec(v_x_988_);
return v_a_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_1035_, size_t v_i_1036_, size_t v_stop_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1036_, v_stop_1037_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1035_, v_i_1036_);
v___x_1041_ = l_Lean_IR_Alt_body(v___x_1040_);
v___x_1042_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1041_, v_b_1038_);
v___x_1043_ = ((size_t)1ULL);
v___x_1044_ = lean_usize_add(v_i_1036_, v___x_1043_);
v_i_1036_ = v___x_1044_;
v_b_1038_ = v___x_1042_;
goto _start;
}
else
{
return v_b_1038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1046_, lean_object* v_i_1047_, lean_object* v_stop_1048_, lean_object* v_b_1049_){
_start:
{
size_t v_i_boxed_1050_; size_t v_stop_boxed_1051_; lean_object* v_res_1052_; 
v_i_boxed_1050_ = lean_unbox_usize(v_i_1047_);
lean_dec(v_i_1047_);
v_stop_boxed_1051_ = lean_unbox_usize(v_stop_1048_);
lean_dec(v_stop_1048_);
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1046_, v_i_boxed_1050_, v_stop_boxed_1051_, v_b_1049_);
lean_dec_ref(v_as_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1053_, lean_object* v_m_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1054_, v_a_1055_, v_b_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1062_, lean_object* v_a_1063_, lean_object* v_x_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1062_, v_a_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec(v_a_1063_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1067_, lean_object* v_data_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1071_, v_b_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1075_, lean_object* v_i_1076_, lean_object* v_source_1077_, lean_object* v_target_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1076_, v_source_1077_, v_target_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1084_, lean_object* v_a_1085_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
lean_object* v_xs_1086_; lean_object* v_body_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_xs_1086_ = lean_ctor_get(v_x_1084_, 1);
lean_inc_ref(v_xs_1086_);
v_body_1087_ = lean_ctor_get(v_x_1084_, 3);
lean_inc(v_body_1087_);
lean_dec_ref_known(v_x_1084_, 5);
v___x_1088_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1087_, v_a_1085_);
v___x_1089_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1086_, v___x_1088_);
lean_dec_ref(v_xs_1086_);
return v___x_1089_;
}
else
{
lean_dec_ref(v_x_1084_);
return v_a_1085_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_unsigned_to_nat(16u);
v___x_1092_ = lean_mk_array(v___x_1091_, v___x_1090_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1100_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1098_, v___x_1099_);
return v___x_1100_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
