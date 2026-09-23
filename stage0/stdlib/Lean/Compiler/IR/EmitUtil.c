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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_nbuckets_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_688_ = lean_array_get_size(v_data_687_);
v___x_689_ = lean_unsigned_to_nat(2u);
v_nbuckets_690_ = lean_nat_mul(v___x_688_, v___x_689_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_box(0);
v___x_693_ = lean_mk_array(v_nbuckets_690_, v___x_692_);
v___x_694_ = lean_array_propagate_mark(v_data_687_, v___x_693_);
v___x_695_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_691_, v_data_687_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_696_, lean_object* v_x_697_){
_start:
{
if (lean_obj_tag(v_x_697_) == 0)
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
else
{
lean_object* v_key_699_; lean_object* v_tail_700_; uint8_t v___x_701_; 
v_key_699_ = lean_ctor_get(v_x_697_, 0);
v_tail_700_ = lean_ctor_get(v_x_697_, 2);
v___x_701_ = l_Lean_IR_instBEqVarId_beq(v_key_699_, v_a_696_);
if (v___x_701_ == 0)
{
v_x_697_ = v_tail_700_;
goto _start;
}
else
{
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_703_, lean_object* v_x_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_703_, v_x_704_);
lean_dec(v_x_704_);
lean_dec(v_a_703_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_707_, lean_object* v_b_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_dec(v_b_708_);
lean_dec(v_a_707_);
return v_x_709_;
}
else
{
lean_object* v_key_710_; lean_object* v_value_711_; lean_object* v_tail_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_724_; 
v_key_710_ = lean_ctor_get(v_x_709_, 0);
v_value_711_ = lean_ctor_get(v_x_709_, 1);
v_tail_712_ = lean_ctor_get(v_x_709_, 2);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_724_ == 0)
{
v___x_714_ = v_x_709_;
v_isShared_715_ = v_isSharedCheck_724_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_tail_712_);
lean_inc(v_value_711_);
lean_inc(v_key_710_);
lean_dec(v_x_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_724_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_IR_instBEqVarId_beq(v_key_710_, v_a_707_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_707_, v_b_708_, v_tail_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 2, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_key_710_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_value_711_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v_value_711_);
lean_dec(v_key_710_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_b_708_);
lean_ctor_set(v___x_714_, 0, v_a_707_);
v___x_722_ = v___x_714_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_707_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_b_708_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_tail_712_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_725_, lean_object* v_a_726_, lean_object* v_b_727_){
_start:
{
lean_object* v_size_728_; lean_object* v_buckets_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_772_; 
v_size_728_ = lean_ctor_get(v_m_725_, 0);
v_buckets_729_ = lean_ctor_get(v_m_725_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_m_725_);
if (v_isSharedCheck_772_ == 0)
{
v___x_731_ = v_m_725_;
v_isShared_732_ = v_isSharedCheck_772_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_buckets_729_);
lean_inc(v_size_728_);
lean_dec(v_m_725_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_772_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v_fold_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; lean_object* v_bkt_746_; uint8_t v___x_747_; 
v___x_733_ = lean_array_get_size(v_buckets_729_);
v___x_734_ = l_Lean_IR_instHashableVarId_hash(v_a_726_);
v___x_735_ = 32ULL;
v___x_736_ = lean_uint64_shift_right(v___x_734_, v___x_735_);
v_fold_737_ = lean_uint64_xor(v___x_734_, v___x_736_);
v___x_738_ = 16ULL;
v___x_739_ = lean_uint64_shift_right(v_fold_737_, v___x_738_);
v___x_740_ = lean_uint64_xor(v_fold_737_, v___x_739_);
v___x_741_ = lean_uint64_to_usize(v___x_740_);
v___x_742_ = lean_usize_of_nat(v___x_733_);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v___x_742_, v___x_743_);
v___x_745_ = lean_usize_land(v___x_741_, v___x_744_);
v_bkt_746_ = lean_array_uget_borrowed(v_buckets_729_, v___x_745_);
v___x_747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_726_, v_bkt_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v_size_x27_749_; lean_object* v___x_750_; lean_object* v_buckets_x27_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v_size_x27_749_ = lean_nat_add(v_size_728_, v___x_748_);
lean_dec(v_size_728_);
lean_inc(v_bkt_746_);
v___x_750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_750_, 0, v_a_726_);
lean_ctor_set(v___x_750_, 1, v_b_727_);
lean_ctor_set(v___x_750_, 2, v_bkt_746_);
v_buckets_x27_751_ = lean_array_uset(v_buckets_729_, v___x_745_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(4u);
v___x_753_ = lean_nat_mul(v_size_x27_749_, v___x_752_);
v___x_754_ = lean_unsigned_to_nat(3u);
v___x_755_ = lean_nat_div(v___x_753_, v___x_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_array_get_size(v_buckets_x27_751_);
v___x_757_ = lean_nat_dec_le(v___x_755_, v___x_756_);
lean_dec(v___x_755_);
if (v___x_757_ == 0)
{
lean_object* v_val_758_; lean_object* v___x_760_; 
v_val_758_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_751_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_val_758_);
lean_ctor_set(v___x_731_, 0, v_size_x27_749_);
v___x_760_ = v___x_731_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_size_x27_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_val_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_object* v___x_763_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_buckets_x27_751_);
lean_ctor_set(v___x_731_, 0, v_size_x27_749_);
v___x_763_ = v___x_731_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_size_x27_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_buckets_x27_751_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v___x_765_; lean_object* v_buckets_x27_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
lean_inc(v_bkt_746_);
v___x_765_ = lean_box(0);
v_buckets_x27_766_ = lean_array_uset(v_buckets_729_, v___x_745_, v___x_765_);
v___x_767_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_726_, v_b_727_, v_bkt_746_);
v___x_768_ = lean_array_uset(v_buckets_x27_766_, v___x_745_, v___x_767_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_768_);
v___x_770_ = v___x_731_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_size_728_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_773_, size_t v_i_774_, size_t v_stop_775_, lean_object* v_b_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_774_, v_stop_775_);
if (v___x_777_ == 0)
{
lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_793_; 
v_fst_778_ = lean_ctor_get(v_b_776_, 0);
v_snd_779_ = lean_ctor_get(v_b_776_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_b_776_);
if (v_isSharedCheck_793_ == 0)
{
v___x_781_ = v_b_776_;
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_snd_779_);
lean_inc(v_fst_778_);
lean_dec(v_b_776_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v_x_784_; lean_object* v_ty_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_783_ = lean_array_uget_borrowed(v_as_773_, v_i_774_);
v_x_784_ = lean_ctor_get(v___x_783_, 0);
v_ty_785_ = lean_ctor_get(v___x_783_, 1);
lean_inc(v_ty_785_);
lean_inc(v_x_784_);
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_778_, v_x_784_, v_ty_785_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_786_);
v___x_788_ = v___x_781_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_snd_779_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
size_t v___x_789_; size_t v___x_790_; 
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_add(v_i_774_, v___x_789_);
v_i_774_ = v___x_790_;
v_b_776_ = v___x_788_;
goto _start;
}
}
}
else
{
return v_b_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_794_, lean_object* v_i_795_, lean_object* v_stop_796_, lean_object* v_b_797_){
_start:
{
size_t v_i_boxed_798_; size_t v_stop_boxed_799_; lean_object* v_res_800_; 
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_stop_boxed_799_ = lean_unbox_usize(v_stop_796_);
lean_dec(v_stop_796_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_794_, v_i_boxed_798_, v_stop_boxed_799_, v_b_797_);
lean_dec_ref(v_as_794_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_801_, lean_object* v_s_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_array_get_size(v_ps_801_);
v___x_805_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
return v_s_802_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = lean_nat_dec_le(v___x_804_, v___x_804_);
if (v___x_806_ == 0)
{
if (v___x_805_ == 0)
{
return v_s_802_;
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_804_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_801_, v___x_807_, v___x_808_, v_s_802_);
return v___x_809_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_804_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_801_, v___x_810_, v___x_811_, v_s_802_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_813_, lean_object* v_s_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_IR_CollectMaps_collectParams(v_ps_813_, v_s_814_);
lean_dec_ref(v_ps_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_816_, lean_object* v_m_817_, lean_object* v_a_818_, lean_object* v_b_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_817_, v_a_818_, v_b_819_);
return v___x_820_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_821_, lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_822_, v_x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_825_, lean_object* v_a_826_, lean_object* v_x_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_825_, v_a_826_, v_x_827_);
lean_dec(v_x_827_);
lean_dec(v_a_826_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_830_, lean_object* v_data_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_833_, lean_object* v_a_834_, lean_object* v_b_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_834_, v_b_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_838_, lean_object* v_i_839_, lean_object* v_source_840_, lean_object* v_target_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_839_, v_source_840_, v_target_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_849_, lean_object* v_xs_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_863_; 
v_fst_852_ = lean_ctor_get(v_x_851_, 0);
v_snd_853_ = lean_ctor_get(v_x_851_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_863_ == 0)
{
v___x_855_ = v_x_851_;
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_inc(v_fst_852_);
lean_dec(v_x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_863_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_857_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_858_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_857_, v___x_858_, v_snd_853_, v_j_849_, v_xs_850_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_859_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_fst_852_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
uint8_t v___x_866_; 
v___x_866_ = 0;
return v___x_866_;
}
else
{
lean_object* v_key_867_; lean_object* v_tail_868_; uint8_t v___x_869_; 
v_key_867_ = lean_ctor_get(v_x_865_, 0);
v_tail_868_ = lean_ctor_get(v_x_865_, 2);
v___x_869_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_867_, v_a_864_);
if (v___x_869_ == 0)
{
v_x_865_ = v_tail_868_;
goto _start;
}
else
{
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_871_, lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_871_, v_x_872_);
lean_dec(v_x_872_);
lean_dec(v_a_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
return v_x_875_;
}
else
{
lean_object* v_key_877_; lean_object* v_value_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_902_; 
v_key_877_ = lean_ctor_get(v_x_876_, 0);
v_value_878_ = lean_ctor_get(v_x_876_, 1);
v_tail_879_ = lean_ctor_get(v_x_876_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_902_ == 0)
{
v___x_881_ = v_x_876_;
v_isShared_882_ = v_isSharedCheck_902_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_inc(v_value_878_);
lean_inc(v_key_877_);
lean_dec(v_x_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_902_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v_fold_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_883_ = lean_array_get_size(v_x_875_);
v___x_884_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_877_);
v___x_885_ = 32ULL;
v___x_886_ = lean_uint64_shift_right(v___x_884_, v___x_885_);
v_fold_887_ = lean_uint64_xor(v___x_884_, v___x_886_);
v___x_888_ = 16ULL;
v___x_889_ = lean_uint64_shift_right(v_fold_887_, v___x_888_);
v___x_890_ = lean_uint64_xor(v_fold_887_, v___x_889_);
v___x_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = lean_usize_of_nat(v___x_883_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_sub(v___x_892_, v___x_893_);
v___x_895_ = lean_usize_land(v___x_891_, v___x_894_);
v___x_896_ = lean_array_uget_borrowed(v_x_875_, v___x_895_);
lean_inc(v___x_896_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 2, v___x_896_);
v___x_898_ = v___x_881_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_key_877_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_value_878_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_896_);
v___x_898_ = v_reuseFailAlloc_901_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_array_uset(v_x_875_, v___x_895_, v___x_898_);
v_x_875_ = v___x_899_;
v_x_876_ = v_tail_879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_903_, lean_object* v_source_904_, lean_object* v_target_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_array_get_size(v_source_904_);
v___x_907_ = lean_nat_dec_lt(v_i_903_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec_ref(v_source_904_);
lean_dec(v_i_903_);
return v_target_905_;
}
else
{
lean_object* v_es_908_; lean_object* v___x_909_; lean_object* v_source_910_; lean_object* v_target_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_es_908_ = lean_array_fget(v_source_904_, v_i_903_);
v___x_909_ = lean_box(0);
v_source_910_ = lean_array_fset(v_source_904_, v_i_903_, v___x_909_);
v_target_911_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_905_, v_es_908_);
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_nat_add(v_i_903_, v___x_912_);
lean_dec(v_i_903_);
v_i_903_ = v___x_913_;
v_source_904_ = v_source_910_;
v_target_905_ = v_target_911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_nbuckets_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_916_ = lean_array_get_size(v_data_915_);
v___x_917_ = lean_unsigned_to_nat(2u);
v_nbuckets_918_ = lean_nat_mul(v___x_916_, v___x_917_);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_box(0);
v___x_921_ = lean_mk_array(v_nbuckets_918_, v___x_920_);
v___x_922_ = lean_array_propagate_mark(v_data_915_, v___x_921_);
v___x_923_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_919_, v_data_915_, v___x_922_);
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
lean_dec_ref_known(v_x_990_, 4);
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
lean_dec_ref_known(v_x_990_, 4);
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
lean_dec_ref_known(v_x_990_, 4);
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
lean_dec_ref_known(v_x_1086_, 5);
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
