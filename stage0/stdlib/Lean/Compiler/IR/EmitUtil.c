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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* v_set_61_; lean_object* v_order_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_set_61_ = lean_ctor_get(v_a_60_, 0);
v_order_62_ = lean_ctor_get(v_a_60_, 1);
v___x_63_ = lean_box(0);
v___x_64_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_61_);
lean_inc(v_f_59_);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_64_, v_f_59_, v_set_61_);
if (v___x_65_ == 0)
{
lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_75_; 
lean_inc_ref(v_order_62_);
lean_inc(v_set_61_);
v_isSharedCheck_75_ = !lean_is_exclusive(v_a_60_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; lean_object* v_unused_77_; 
v_unused_76_ = lean_ctor_get(v_a_60_, 1);
lean_dec(v_unused_76_);
v_unused_77_ = lean_ctor_get(v_a_60_, 0);
lean_dec(v_unused_77_);
v___x_67_ = v_a_60_;
v_isShared_68_ = v_isSharedCheck_75_;
goto v_resetjp_66_;
}
else
{
lean_dec(v_a_60_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_75_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
lean_inc(v_f_59_);
v___x_69_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_64_, v_f_59_, v___x_63_, v_set_61_);
v___x_70_ = lean_array_push(v_order_62_, v_f_59_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_70_);
lean_ctor_set(v___x_67_, 0, v___x_69_);
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_74_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_63_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
}
}
else
{
lean_object* v___x_78_; 
lean_dec(v_f_59_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_63_);
lean_ctor_set(v___x_78_, 1, v_a_60_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* v_f_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_set_82_; lean_object* v_order_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_set_82_ = lean_ctor_get(v_a_81_, 0);
v_order_83_ = lean_ctor_get(v_a_81_, 1);
v___x_84_ = lean_box(0);
v___x_85_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_82_);
lean_inc(v_f_79_);
v___x_86_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_85_, v_f_79_, v_set_82_);
if (v___x_86_ == 0)
{
lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_96_; 
lean_inc_ref(v_order_83_);
lean_inc(v_set_82_);
v_isSharedCheck_96_ = !lean_is_exclusive(v_a_81_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; lean_object* v_unused_98_; 
v_unused_97_ = lean_ctor_get(v_a_81_, 1);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_a_81_, 0);
lean_dec(v_unused_98_);
v___x_88_ = v_a_81_;
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
else
{
lean_dec(v_a_81_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
lean_inc(v_f_79_);
v___x_90_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_85_, v_f_79_, v___x_84_, v_set_82_);
v___x_91_ = lean_array_push(v_order_83_, v_f_79_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v___x_91_);
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_95_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_84_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
return v___x_94_;
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v_f_79_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_84_);
lean_ctor_set(v___x_99_, 1, v_a_81_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* v_f_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_IR_CollectUsedDecls_collect(v_f_100_, v_a_101_, v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object* v_k_104_, lean_object* v_v_105_, lean_object* v_t_106_){
_start:
{
if (lean_obj_tag(v_t_106_) == 0)
{
lean_object* v_size_107_; lean_object* v_k_108_; lean_object* v_v_109_; lean_object* v_l_110_; lean_object* v_r_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_391_; 
v_size_107_ = lean_ctor_get(v_t_106_, 0);
v_k_108_ = lean_ctor_get(v_t_106_, 1);
v_v_109_ = lean_ctor_get(v_t_106_, 2);
v_l_110_ = lean_ctor_get(v_t_106_, 3);
v_r_111_ = lean_ctor_get(v_t_106_, 4);
v_isSharedCheck_391_ = !lean_is_exclusive(v_t_106_);
if (v_isSharedCheck_391_ == 0)
{
v___x_113_ = v_t_106_;
v_isShared_114_ = v_isSharedCheck_391_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_r_111_);
lean_inc(v_l_110_);
lean_inc(v_v_109_);
lean_inc(v_k_108_);
lean_inc(v_size_107_);
lean_dec(v_t_106_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_391_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; 
v___x_115_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_104_, v_k_108_);
switch(v___x_115_)
{
case 0:
{
lean_object* v_impl_116_; lean_object* v___x_117_; 
lean_dec(v_size_107_);
v_impl_116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_104_, v_v_105_, v_l_110_);
v___x_117_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_111_) == 0)
{
lean_object* v_size_118_; lean_object* v_size_119_; lean_object* v_k_120_; lean_object* v_v_121_; lean_object* v_l_122_; lean_object* v_r_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_size_118_ = lean_ctor_get(v_r_111_, 0);
v_size_119_ = lean_ctor_get(v_impl_116_, 0);
v_k_120_ = lean_ctor_get(v_impl_116_, 1);
v_v_121_ = lean_ctor_get(v_impl_116_, 2);
v_l_122_ = lean_ctor_get(v_impl_116_, 3);
v_r_123_ = lean_ctor_get(v_impl_116_, 4);
lean_inc(v_r_123_);
v___x_124_ = lean_unsigned_to_nat(3u);
v___x_125_ = lean_nat_mul(v___x_124_, v_size_118_);
v___x_126_ = lean_nat_dec_lt(v___x_125_, v_size_119_);
lean_dec(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v_r_123_);
v___x_127_ = lean_nat_add(v___x_117_, v_size_119_);
v___x_128_ = lean_nat_add(v___x_127_, v_size_118_);
lean_dec(v___x_127_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 3, v_impl_116_);
lean_ctor_set(v___x_113_, 0, v___x_128_);
v___x_130_ = v___x_113_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_impl_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_r_111_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
else
{
lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_197_; 
lean_inc(v_l_122_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
lean_inc(v_size_119_);
v_isSharedCheck_197_ = !lean_is_exclusive(v_impl_116_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; lean_object* v_unused_199_; lean_object* v_unused_200_; lean_object* v_unused_201_; lean_object* v_unused_202_; 
v_unused_198_ = lean_ctor_get(v_impl_116_, 4);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_impl_116_, 3);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_impl_116_, 2);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_impl_116_, 1);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_impl_116_, 0);
lean_dec(v_unused_202_);
v___x_133_ = v_impl_116_;
v_isShared_134_ = v_isSharedCheck_197_;
goto v_resetjp_132_;
}
else
{
lean_dec(v_impl_116_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_197_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v_size_135_; lean_object* v_size_136_; lean_object* v_k_137_; lean_object* v_v_138_; lean_object* v_l_139_; lean_object* v_r_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_size_135_ = lean_ctor_get(v_l_122_, 0);
v_size_136_ = lean_ctor_get(v_r_123_, 0);
v_k_137_ = lean_ctor_get(v_r_123_, 1);
v_v_138_ = lean_ctor_get(v_r_123_, 2);
v_l_139_ = lean_ctor_get(v_r_123_, 3);
v_r_140_ = lean_ctor_get(v_r_123_, 4);
v___x_141_ = lean_unsigned_to_nat(2u);
v___x_142_ = lean_nat_mul(v___x_141_, v_size_135_);
v___x_143_ = lean_nat_dec_lt(v_size_136_, v___x_142_);
lean_dec(v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_172_; 
lean_inc(v_r_140_);
lean_inc(v_l_139_);
lean_inc(v_v_138_);
lean_inc(v_k_137_);
v_isSharedCheck_172_ = !lean_is_exclusive(v_r_123_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; 
v_unused_173_ = lean_ctor_get(v_r_123_, 4);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_123_, 3);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_r_123_, 2);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_r_123_, 1);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_123_, 0);
lean_dec(v_unused_177_);
v___x_145_ = v_r_123_;
v_isShared_146_ = v_isSharedCheck_172_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_r_123_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_172_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___x_160_; lean_object* v___y_162_; 
v___x_147_ = lean_nat_add(v___x_117_, v_size_119_);
lean_dec(v_size_119_);
v___x_148_ = lean_nat_add(v___x_147_, v_size_118_);
lean_dec(v___x_147_);
v___x_160_ = lean_nat_add(v___x_117_, v_size_135_);
if (lean_obj_tag(v_l_139_) == 0)
{
lean_object* v_size_170_; 
v_size_170_ = lean_ctor_get(v_l_139_, 0);
lean_inc(v_size_170_);
v___y_162_ = v_size_170_;
goto v___jp_161_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v___y_162_ = v___x_171_;
goto v___jp_161_;
}
v___jp_149_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_nat_add(v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec(v___y_151_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_r_111_);
lean_ctor_set(v___x_145_, 3, v_r_140_);
lean_ctor_set(v___x_145_, 2, v_v_109_);
lean_ctor_set(v___x_145_, 1, v_k_108_);
lean_ctor_set(v___x_145_, 0, v___x_153_);
v___x_155_ = v___x_145_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v_r_140_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v_r_111_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 4, v___x_155_);
lean_ctor_set(v___x_133_, 3, v___y_150_);
lean_ctor_set(v___x_133_, 2, v_v_138_);
lean_ctor_set(v___x_133_, 1, v_k_137_);
lean_ctor_set(v___x_133_, 0, v___x_148_);
v___x_157_ = v___x_133_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_k_137_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_v_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v___y_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_nat_add(v___x_160_, v___y_162_);
lean_dec(v___y_162_);
lean_dec(v___x_160_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v_l_139_);
lean_ctor_set(v___x_113_, 3, v_l_122_);
lean_ctor_set(v___x_113_, 2, v_v_121_);
lean_ctor_set(v___x_113_, 1, v_k_120_);
lean_ctor_set(v___x_113_, 0, v___x_163_);
v___x_165_ = v___x_113_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_l_122_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_l_139_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_nat_add(v___x_117_, v_size_118_);
if (lean_obj_tag(v_r_140_) == 0)
{
lean_object* v_size_167_; 
v_size_167_ = lean_ctor_get(v_r_140_, 0);
lean_inc(v_size_167_);
v___y_150_ = v___x_165_;
v___y_151_ = v___x_166_;
v___y_152_ = v_size_167_;
goto v___jp_149_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___y_150_ = v___x_165_;
v___y_151_ = v___x_166_;
v___y_152_ = v___x_168_;
goto v___jp_149_;
}
}
}
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
lean_del_object(v___x_113_);
v___x_178_ = lean_nat_add(v___x_117_, v_size_119_);
lean_dec(v_size_119_);
v___x_179_ = lean_nat_add(v___x_178_, v_size_118_);
lean_dec(v___x_178_);
v___x_180_ = lean_nat_add(v___x_117_, v_size_118_);
v___x_181_ = lean_nat_add(v___x_180_, v_size_136_);
lean_dec(v___x_180_);
lean_inc_ref(v_r_111_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 4, v_r_111_);
lean_ctor_set(v___x_133_, 3, v_r_123_);
lean_ctor_set(v___x_133_, 2, v_v_109_);
lean_ctor_set(v___x_133_, 1, v_k_108_);
lean_ctor_set(v___x_133_, 0, v___x_181_);
v___x_183_ = v___x_133_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_r_123_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_r_111_);
v___x_183_ = v_reuseFailAlloc_196_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_isSharedCheck_190_ = !lean_is_exclusive(v_r_111_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_191_ = lean_ctor_get(v_r_111_, 4);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_r_111_, 3);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_r_111_, 2);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_r_111_, 1);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_r_111_, 0);
lean_dec(v_unused_195_);
v___x_185_ = v_r_111_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_dec(v_r_111_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 4, v___x_183_);
lean_ctor_set(v___x_185_, 3, v_l_122_);
lean_ctor_set(v___x_185_, 2, v_v_121_);
lean_ctor_set(v___x_185_, 1, v_k_120_);
lean_ctor_set(v___x_185_, 0, v___x_179_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_189_, 3, v_l_122_);
lean_ctor_set(v_reuseFailAlloc_189_, 4, v___x_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_203_; 
v_l_203_ = lean_ctor_get(v_impl_116_, 3);
if (lean_obj_tag(v_l_203_) == 0)
{
lean_object* v_r_204_; lean_object* v_k_205_; lean_object* v_v_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_217_; 
lean_inc_ref(v_l_203_);
v_r_204_ = lean_ctor_get(v_impl_116_, 4);
v_k_205_ = lean_ctor_get(v_impl_116_, 1);
v_v_206_ = lean_ctor_get(v_impl_116_, 2);
v_isSharedCheck_217_ = !lean_is_exclusive(v_impl_116_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; lean_object* v_unused_219_; 
v_unused_218_ = lean_ctor_get(v_impl_116_, 3);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_impl_116_, 0);
lean_dec(v_unused_219_);
v___x_208_ = v_impl_116_;
v_isShared_209_ = v_isSharedCheck_217_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_r_204_);
lean_inc(v_v_206_);
lean_inc(v_k_205_);
lean_dec(v_impl_116_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_217_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_204_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 3, v_r_204_);
lean_ctor_set(v___x_208_, 2, v_v_109_);
lean_ctor_set(v___x_208_, 1, v_k_108_);
lean_ctor_set(v___x_208_, 0, v___x_117_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_216_, 3, v_r_204_);
lean_ctor_set(v_reuseFailAlloc_216_, 4, v_r_204_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v___x_212_);
lean_ctor_set(v___x_113_, 3, v_l_203_);
lean_ctor_set(v___x_113_, 2, v_v_206_);
lean_ctor_set(v___x_113_, 1, v_k_205_);
lean_ctor_set(v___x_113_, 0, v___x_210_);
v___x_214_ = v___x_113_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_206_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_l_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v_r_220_; 
v_r_220_ = lean_ctor_get(v_impl_116_, 4);
lean_inc(v_r_220_);
if (lean_obj_tag(v_r_220_) == 0)
{
lean_object* v_k_221_; lean_object* v_v_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_245_; 
lean_inc(v_l_203_);
v_k_221_ = lean_ctor_get(v_impl_116_, 1);
v_v_222_ = lean_ctor_get(v_impl_116_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v_impl_116_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_246_ = lean_ctor_get(v_impl_116_, 4);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_impl_116_, 3);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_impl_116_, 0);
lean_dec(v_unused_248_);
v___x_224_ = v_impl_116_;
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_v_222_);
lean_inc(v_k_221_);
lean_dec(v_impl_116_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_245_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_k_226_; lean_object* v_v_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
v_k_226_ = lean_ctor_get(v_r_220_, 1);
v_v_227_ = lean_ctor_get(v_r_220_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_r_220_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_242_ = lean_ctor_get(v_r_220_, 4);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_r_220_, 3);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_r_220_, 0);
lean_dec(v_unused_244_);
v___x_229_ = v_r_220_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_v_227_);
lean_inc(v_k_226_);
lean_dec(v_r_220_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(3u);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v_l_203_);
lean_ctor_set(v___x_229_, 3, v_l_203_);
lean_ctor_set(v___x_229_, 2, v_v_222_);
lean_ctor_set(v___x_229_, 1, v_k_221_);
lean_ctor_set(v___x_229_, 0, v___x_117_);
v___x_233_ = v___x_229_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_221_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_222_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_l_203_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_l_203_);
v___x_233_ = v_reuseFailAlloc_240_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 4, v_l_203_);
lean_ctor_set(v___x_224_, 2, v_v_109_);
lean_ctor_set(v___x_224_, 1, v_k_108_);
lean_ctor_set(v___x_224_, 0, v___x_117_);
v___x_235_ = v___x_224_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_l_203_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_l_203_);
v___x_235_ = v_reuseFailAlloc_239_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v___x_235_);
lean_ctor_set(v___x_113_, 3, v___x_233_);
lean_ctor_set(v___x_113_, 2, v_v_227_);
lean_ctor_set(v___x_113_, 1, v_k_226_);
lean_ctor_set(v___x_113_, 0, v___x_231_);
v___x_237_ = v___x_113_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_226_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = lean_unsigned_to_nat(2u);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v_r_220_);
lean_ctor_set(v___x_113_, 3, v_impl_116_);
lean_ctor_set(v___x_113_, 0, v___x_249_);
v___x_251_ = v___x_113_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_impl_116_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_r_220_);
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
case 1:
{
lean_object* v___x_254_; 
lean_dec(v_v_109_);
lean_dec(v_k_108_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 2, v_v_105_);
lean_ctor_set(v___x_113_, 1, v_k_104_);
v___x_254_ = v___x_113_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_size_107_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_104_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_v_105_);
lean_ctor_set(v_reuseFailAlloc_255_, 3, v_l_110_);
lean_ctor_set(v_reuseFailAlloc_255_, 4, v_r_111_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
default: 
{
lean_object* v_impl_256_; lean_object* v___x_257_; 
lean_dec(v_size_107_);
v_impl_256_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_104_, v_v_105_, v_r_111_);
v___x_257_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_110_) == 0)
{
lean_object* v_size_258_; lean_object* v_size_259_; lean_object* v_k_260_; lean_object* v_v_261_; lean_object* v_l_262_; lean_object* v_r_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_size_258_ = lean_ctor_get(v_l_110_, 0);
v_size_259_ = lean_ctor_get(v_impl_256_, 0);
v_k_260_ = lean_ctor_get(v_impl_256_, 1);
v_v_261_ = lean_ctor_get(v_impl_256_, 2);
v_l_262_ = lean_ctor_get(v_impl_256_, 3);
lean_inc(v_l_262_);
v_r_263_ = lean_ctor_get(v_impl_256_, 4);
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = lean_nat_mul(v___x_264_, v_size_258_);
v___x_266_ = lean_nat_dec_lt(v___x_265_, v_size_259_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
lean_dec(v_l_262_);
v___x_267_ = lean_nat_add(v___x_257_, v_size_258_);
v___x_268_ = lean_nat_add(v___x_267_, v_size_259_);
lean_dec(v___x_267_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v_impl_256_);
lean_ctor_set(v___x_113_, 0, v___x_268_);
v___x_270_ = v___x_113_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_271_, 3, v_l_110_);
lean_ctor_set(v_reuseFailAlloc_271_, 4, v_impl_256_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_335_; 
lean_inc(v_r_263_);
lean_inc(v_v_261_);
lean_inc(v_k_260_);
lean_inc(v_size_259_);
v_isSharedCheck_335_ = !lean_is_exclusive(v_impl_256_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; lean_object* v_unused_337_; lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; 
v_unused_336_ = lean_ctor_get(v_impl_256_, 4);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_impl_256_, 3);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_impl_256_, 2);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_impl_256_, 1);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_impl_256_, 0);
lean_dec(v_unused_340_);
v___x_273_ = v_impl_256_;
v_isShared_274_ = v_isSharedCheck_335_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_impl_256_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_335_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_size_275_; lean_object* v_k_276_; lean_object* v_v_277_; lean_object* v_l_278_; lean_object* v_r_279_; lean_object* v_size_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_size_275_ = lean_ctor_get(v_l_262_, 0);
v_k_276_ = lean_ctor_get(v_l_262_, 1);
v_v_277_ = lean_ctor_get(v_l_262_, 2);
v_l_278_ = lean_ctor_get(v_l_262_, 3);
v_r_279_ = lean_ctor_get(v_l_262_, 4);
v_size_280_ = lean_ctor_get(v_r_263_, 0);
v___x_281_ = lean_unsigned_to_nat(2u);
v___x_282_ = lean_nat_mul(v___x_281_, v_size_280_);
v___x_283_ = lean_nat_dec_lt(v_size_275_, v___x_282_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_311_; 
lean_inc(v_r_279_);
lean_inc(v_l_278_);
lean_inc(v_v_277_);
lean_inc(v_k_276_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_l_262_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_312_ = lean_ctor_get(v_l_262_, 4);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_262_, 3);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_262_, 2);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_l_262_, 1);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_l_262_, 0);
lean_dec(v_unused_316_);
v___x_285_ = v_l_262_;
v_isShared_286_ = v_isSharedCheck_311_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_l_262_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_311_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_301_; 
v___x_287_ = lean_nat_add(v___x_257_, v_size_258_);
v___x_288_ = lean_nat_add(v___x_287_, v_size_259_);
lean_dec(v_size_259_);
if (lean_obj_tag(v_l_278_) == 0)
{
lean_object* v_size_309_; 
v_size_309_ = lean_ctor_get(v_l_278_, 0);
lean_inc(v_size_309_);
v___y_301_ = v_size_309_;
goto v___jp_300_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_unsigned_to_nat(0u);
v___y_301_ = v___x_310_;
goto v___jp_300_;
}
v___jp_289_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_nat_add(v___y_290_, v___y_292_);
lean_dec(v___y_292_);
lean_dec(v___y_290_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 4, v_r_263_);
lean_ctor_set(v___x_285_, 3, v_r_279_);
lean_ctor_set(v___x_285_, 2, v_v_261_);
lean_ctor_set(v___x_285_, 1, v_k_260_);
lean_ctor_set(v___x_285_, 0, v___x_293_);
v___x_295_ = v___x_285_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_k_260_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_v_261_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_r_279_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_r_263_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 4, v___x_295_);
lean_ctor_set(v___x_273_, 3, v___y_291_);
lean_ctor_set(v___x_273_, 2, v_v_277_);
lean_ctor_set(v___x_273_, 1, v_k_276_);
lean_ctor_set(v___x_273_, 0, v___x_288_);
v___x_297_ = v___x_273_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_276_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_277_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v___y_291_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = lean_nat_add(v___x_287_, v___y_301_);
lean_dec(v___y_301_);
lean_dec(v___x_287_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v_l_278_);
lean_ctor_set(v___x_113_, 0, v___x_302_);
v___x_304_ = v___x_113_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_l_110_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_l_278_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_nat_add(v___x_257_, v_size_280_);
if (lean_obj_tag(v_r_279_) == 0)
{
lean_object* v_size_306_; 
v_size_306_ = lean_ctor_get(v_r_279_, 0);
lean_inc(v_size_306_);
v___y_290_ = v___x_305_;
v___y_291_ = v___x_304_;
v___y_292_ = v_size_306_;
goto v___jp_289_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___y_290_ = v___x_305_;
v___y_291_ = v___x_304_;
v___y_292_ = v___x_307_;
goto v___jp_289_;
}
}
}
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
lean_del_object(v___x_113_);
v___x_317_ = lean_nat_add(v___x_257_, v_size_258_);
v___x_318_ = lean_nat_add(v___x_317_, v_size_259_);
lean_dec(v_size_259_);
v___x_319_ = lean_nat_add(v___x_317_, v_size_275_);
lean_dec(v___x_317_);
lean_inc_ref(v_l_110_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 4, v_l_262_);
lean_ctor_set(v___x_273_, 3, v_l_110_);
lean_ctor_set(v___x_273_, 2, v_v_109_);
lean_ctor_set(v___x_273_, 1, v_k_108_);
lean_ctor_set(v___x_273_, 0, v___x_319_);
v___x_321_ = v___x_273_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_l_110_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_l_262_);
v___x_321_ = v_reuseFailAlloc_334_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_isSharedCheck_328_ = !lean_is_exclusive(v_l_110_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; 
v_unused_329_ = lean_ctor_get(v_l_110_, 4);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_110_, 3);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_110_, 2);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_l_110_, 1);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_l_110_, 0);
lean_dec(v_unused_333_);
v___x_323_ = v_l_110_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_dec(v_l_110_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v_r_263_);
lean_ctor_set(v___x_323_, 3, v___x_321_);
lean_ctor_set(v___x_323_, 2, v_v_261_);
lean_ctor_set(v___x_323_, 1, v_k_260_);
lean_ctor_set(v___x_323_, 0, v___x_318_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_k_260_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_v_261_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_r_263_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_341_; 
v_l_341_ = lean_ctor_get(v_impl_256_, 3);
lean_inc(v_l_341_);
if (lean_obj_tag(v_l_341_) == 0)
{
lean_object* v_r_342_; lean_object* v_k_343_; lean_object* v_v_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_367_; 
v_r_342_ = lean_ctor_get(v_impl_256_, 4);
v_k_343_ = lean_ctor_get(v_impl_256_, 1);
v_v_344_ = lean_ctor_get(v_impl_256_, 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_impl_256_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; lean_object* v_unused_369_; 
v_unused_368_ = lean_ctor_get(v_impl_256_, 3);
lean_dec(v_unused_368_);
v_unused_369_ = lean_ctor_get(v_impl_256_, 0);
lean_dec(v_unused_369_);
v___x_346_ = v_impl_256_;
v_isShared_347_ = v_isSharedCheck_367_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_r_342_);
lean_inc(v_v_344_);
lean_inc(v_k_343_);
lean_dec(v_impl_256_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_367_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_k_348_; lean_object* v_v_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_363_; 
v_k_348_ = lean_ctor_get(v_l_341_, 1);
v_v_349_ = lean_ctor_get(v_l_341_, 2);
v_isSharedCheck_363_ = !lean_is_exclusive(v_l_341_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; lean_object* v_unused_366_; 
v_unused_364_ = lean_ctor_get(v_l_341_, 4);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_l_341_, 3);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_l_341_, 0);
lean_dec(v_unused_366_);
v___x_351_ = v_l_341_;
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_v_349_);
lean_inc(v_k_348_);
lean_dec(v_l_341_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_342_, 2);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 4, v_r_342_);
lean_ctor_set(v___x_351_, 3, v_r_342_);
lean_ctor_set(v___x_351_, 2, v_v_109_);
lean_ctor_set(v___x_351_, 1, v_k_108_);
lean_ctor_set(v___x_351_, 0, v___x_257_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_r_342_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_r_342_);
v___x_355_ = v_reuseFailAlloc_362_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
lean_inc(v_r_342_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 3, v_r_342_);
lean_ctor_set(v___x_346_, 0, v___x_257_);
v___x_357_ = v___x_346_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_k_343_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_r_342_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_r_342_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v___x_357_);
lean_ctor_set(v___x_113_, 3, v___x_355_);
lean_ctor_set(v___x_113_, 2, v_v_349_);
lean_ctor_set(v___x_113_, 1, v_k_348_);
lean_ctor_set(v___x_113_, 0, v___x_353_);
v___x_359_ = v___x_113_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_348_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_349_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
else
{
lean_object* v_r_370_; 
v_r_370_ = lean_ctor_get(v_impl_256_, 4);
lean_inc(v_r_370_);
if (lean_obj_tag(v_r_370_) == 0)
{
lean_object* v_k_371_; lean_object* v_v_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_383_; 
v_k_371_ = lean_ctor_get(v_impl_256_, 1);
v_v_372_ = lean_ctor_get(v_impl_256_, 2);
v_isSharedCheck_383_ = !lean_is_exclusive(v_impl_256_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; 
v_unused_384_ = lean_ctor_get(v_impl_256_, 4);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_impl_256_, 3);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_impl_256_, 0);
lean_dec(v_unused_386_);
v___x_374_ = v_impl_256_;
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_v_372_);
lean_inc(v_k_371_);
lean_dec(v_impl_256_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_unsigned_to_nat(3u);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 4, v_l_341_);
lean_ctor_set(v___x_374_, 2, v_v_109_);
lean_ctor_set(v___x_374_, 1, v_k_108_);
lean_ctor_set(v___x_374_, 0, v___x_257_);
v___x_378_ = v___x_374_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_l_341_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v_l_341_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v_r_370_);
lean_ctor_set(v___x_113_, 3, v___x_378_);
lean_ctor_set(v___x_113_, 2, v_v_372_);
lean_ctor_set(v___x_113_, 1, v_k_371_);
lean_ctor_set(v___x_113_, 0, v___x_376_);
v___x_380_ = v___x_113_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_k_371_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_v_372_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_r_370_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_unsigned_to_nat(2u);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 4, v_impl_256_);
lean_ctor_set(v___x_113_, 3, v_r_370_);
lean_ctor_set(v___x_113_, 0, v___x_387_);
v___x_389_ = v___x_113_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_v_109_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_r_370_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v_impl_256_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
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
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_k_104_);
lean_ctor_set(v___x_393_, 2, v_v_105_);
lean_ctor_set(v___x_393_, 3, v_t_106_);
lean_ctor_set(v___x_393_, 4, v_t_106_);
return v___x_393_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object* v_k_394_, lean_object* v_t_395_){
_start:
{
if (lean_obj_tag(v_t_395_) == 0)
{
lean_object* v_k_396_; lean_object* v_l_397_; lean_object* v_r_398_; uint8_t v___x_399_; 
v_k_396_ = lean_ctor_get(v_t_395_, 1);
v_l_397_ = lean_ctor_get(v_t_395_, 3);
v_r_398_ = lean_ctor_get(v_t_395_, 4);
v___x_399_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_394_, v_k_396_);
switch(v___x_399_)
{
case 0:
{
v_t_395_ = v_l_397_;
goto _start;
}
case 1:
{
uint8_t v___x_401_; 
v___x_401_ = 1;
return v___x_401_;
}
default: 
{
v_t_395_ = v_r_398_;
goto _start;
}
}
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object* v_k_404_, lean_object* v_t_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_404_, v_t_405_);
lean_dec(v_t_405_);
lean_dec(v_k_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* v_x_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
switch(lean_obj_tag(v_x_408_))
{
case 0:
{
lean_object* v_e_411_; lean_object* v_b_412_; lean_object* v_f_414_; lean_object* v___y_415_; lean_object* v___y_416_; 
v_e_411_ = lean_ctor_get(v_x_408_, 2);
lean_inc_ref(v_e_411_);
v_b_412_ = lean_ctor_get(v_x_408_, 3);
lean_inc(v_b_412_);
lean_dec_ref_known(v_x_408_, 4);
switch(lean_obj_tag(v_e_411_))
{
case 6:
{
lean_object* v_c_434_; 
v_c_434_ = lean_ctor_get(v_e_411_, 0);
lean_inc(v_c_434_);
lean_dec_ref_known(v_e_411_, 2);
v_f_414_ = v_c_434_;
v___y_415_ = v_a_409_;
v___y_416_ = v_a_410_;
goto v___jp_413_;
}
case 7:
{
lean_object* v_c_435_; 
v_c_435_ = lean_ctor_get(v_e_411_, 0);
lean_inc(v_c_435_);
lean_dec_ref_known(v_e_411_, 2);
v_f_414_ = v_c_435_;
v___y_415_ = v_a_409_;
v___y_416_ = v_a_410_;
goto v___jp_413_;
}
default: 
{
lean_dec_ref(v_e_411_);
v_x_408_ = v_b_412_;
goto _start;
}
}
v___jp_413_:
{
lean_object* v_set_417_; lean_object* v_order_418_; uint8_t v___x_419_; 
v_set_417_ = lean_ctor_get(v___y_416_, 0);
v_order_418_ = lean_ctor_get(v___y_416_, 1);
v___x_419_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_f_414_, v_set_417_);
if (v___x_419_ == 0)
{
lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
lean_inc_ref(v_order_418_);
lean_inc(v_set_417_);
v_isSharedCheck_430_ = !lean_is_exclusive(v___y_416_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_431_ = lean_ctor_get(v___y_416_, 1);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v___y_416_, 0);
lean_dec(v_unused_432_);
v___x_421_ = v___y_416_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_dec(v___y_416_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_423_ = lean_box(0);
lean_inc(v_f_414_);
v___x_424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_f_414_, v___x_423_, v_set_417_);
v___x_425_ = lean_array_push(v_order_418_, v_f_414_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_425_);
lean_ctor_set(v___x_421_, 0, v___x_424_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_429_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
v_x_408_ = v_b_412_;
v_a_409_ = v___y_415_;
v_a_410_ = v___x_427_;
goto _start;
}
}
}
else
{
lean_dec(v_f_414_);
v_x_408_ = v_b_412_;
v_a_409_ = v___y_415_;
v_a_410_ = v___y_416_;
goto _start;
}
}
}
case 1:
{
lean_object* v_v_437_; lean_object* v_b_438_; lean_object* v___x_439_; lean_object* v_snd_440_; 
v_v_437_ = lean_ctor_get(v_x_408_, 2);
lean_inc(v_v_437_);
v_b_438_ = lean_ctor_get(v_x_408_, 3);
lean_inc(v_b_438_);
lean_dec_ref_known(v_x_408_, 4);
v___x_439_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_437_, v_a_409_, v_a_410_);
v_snd_440_ = lean_ctor_get(v___x_439_, 1);
lean_inc(v_snd_440_);
lean_dec_ref(v___x_439_);
v_x_408_ = v_b_438_;
v_a_410_ = v_snd_440_;
goto _start;
}
case 9:
{
lean_object* v_cs_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_cs_442_ = lean_ctor_get(v_x_408_, 3);
lean_inc_ref(v_cs_442_);
lean_dec_ref_known(v_x_408_, 4);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_array_get_size(v_cs_442_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_nat_dec_lt(v___x_443_, v___x_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v_cs_442_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v_a_410_);
return v___x_447_;
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_444_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_442_, v___x_448_, v___x_449_, v___x_445_, v_a_409_, v_a_410_);
lean_dec_ref(v_cs_442_);
return v___x_450_;
}
}
default: 
{
uint8_t v___x_451_; 
v___x_451_ = l_Lean_IR_FnBody_isTerminal(v_x_408_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_IR_FnBody_body(v_x_408_);
lean_dec(v_x_408_);
v_x_408_ = v___x_452_;
goto _start;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_x_408_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_a_410_);
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object* v_as_456_, size_t v_i_457_, size_t v_stop_458_, lean_object* v_b_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_usize_dec_eq(v_i_457_, v_stop_458_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; size_t v___x_468_; size_t v___x_469_; 
v___x_463_ = lean_array_uget_borrowed(v_as_456_, v_i_457_);
v___x_464_ = l_Lean_IR_Alt_body(v___x_463_);
v___x_465_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v___x_464_, v___y_460_, v___y_461_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_fst_466_);
v_snd_467_ = lean_ctor_get(v___x_465_, 1);
lean_inc(v_snd_467_);
lean_dec_ref(v___x_465_);
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_add(v_i_457_, v___x_468_);
v_i_457_ = v___x_469_;
v_b_459_ = v_fst_466_;
v___y_461_ = v_snd_467_;
goto _start;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_b_459_);
lean_ctor_set(v___x_471_, 1, v___y_461_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_stop_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
size_t v_i_boxed_478_; size_t v_stop_boxed_479_; lean_object* v_res_480_; 
v_i_boxed_478_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_stop_boxed_479_ = lean_unbox_usize(v_stop_474_);
lean_dec(v_stop_474_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_472_, v_i_boxed_478_, v_stop_boxed_479_, v_b_475_, v___y_476_, v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v_as_472_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* v_x_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_481_, v_a_482_, v_a_483_);
lean_dec_ref(v_a_482_);
return v_res_484_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object* v_00_u03b2_485_, lean_object* v_k_486_, lean_object* v_t_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_486_, v_t_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_489_, lean_object* v_k_490_, lean_object* v_t_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_489_, v_k_490_, v_t_491_);
lean_dec(v_t_491_);
lean_dec(v_k_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object* v_00_u03b2_494_, lean_object* v_k_495_, lean_object* v_v_496_, lean_object* v_t_497_, lean_object* v_hl_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_495_, v_v_496_, v_t_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* v_fn_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; 
lean_inc_ref(v_a_501_);
v___x_503_ = lean_get_init_fn_name_for(v_a_501_, v_fn_500_);
if (lean_obj_tag(v___x_503_) == 1)
{
lean_object* v_val_504_; lean_object* v_set_505_; lean_object* v_order_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_val_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_503_, 1);
v_set_505_ = lean_ctor_get(v_a_502_, 0);
v_order_506_ = lean_ctor_get(v_a_502_, 1);
v___x_507_ = lean_box(0);
v___x_508_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_504_, v_set_505_);
if (v___x_508_ == 0)
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
lean_inc_ref(v_order_506_);
lean_inc(v_set_505_);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_502_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; lean_object* v_unused_520_; 
v_unused_519_ = lean_ctor_get(v_a_502_, 1);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_a_502_, 0);
lean_dec(v_unused_520_);
v___x_510_ = v_a_502_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_a_502_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
lean_inc(v_val_504_);
v___x_512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_504_, v___x_507_, v_set_505_);
v___x_513_ = lean_array_push(v_order_506_, v_val_504_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_513_);
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_507_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
}
}
else
{
lean_object* v___x_521_; 
lean_dec(v_val_504_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_507_);
lean_ctor_set(v___x_521_, 1, v_a_502_);
return v___x_521_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v___x_503_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_a_502_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object* v_fn_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_524_, v_a_525_, v_a_526_);
lean_dec_ref(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_f_531_; lean_object* v_body_532_; lean_object* v___x_533_; lean_object* v_snd_534_; lean_object* v___x_535_; 
v_f_531_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_f_531_);
v_body_532_ = lean_ctor_get(v_x_528_, 3);
lean_inc(v_body_532_);
lean_dec_ref_known(v_x_528_, 5);
v___x_533_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_531_, v_a_529_, v_a_530_);
v_snd_534_ = lean_ctor_get(v___x_533_, 1);
lean_inc(v_snd_534_);
lean_dec_ref(v___x_533_);
v___x_535_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_532_, v_a_529_, v_snd_534_);
return v___x_535_;
}
else
{
lean_object* v_f_536_; lean_object* v___x_537_; 
v_f_536_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_f_536_);
lean_dec_ref_known(v_x_528_, 4);
v___x_537_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_536_, v_a_529_, v_a_530_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object* v_x_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_538_, v_a_539_, v_a_540_);
lean_dec_ref(v_a_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
if (lean_obj_tag(v_as_542_) == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___y_544_);
return v___x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v_tail_548_; lean_object* v___x_549_; lean_object* v_snd_550_; lean_object* v_set_551_; lean_object* v_order_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_head_547_ = lean_ctor_get(v_as_542_, 0);
lean_inc_n(v_head_547_, 2);
v_tail_548_ = lean_ctor_get(v_as_542_, 1);
lean_inc(v_tail_548_);
lean_dec_ref_known(v_as_542_, 2);
v___x_549_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_547_, v___y_543_, v___y_544_);
v_snd_550_ = lean_ctor_get(v___x_549_, 1);
lean_inc(v_snd_550_);
lean_dec_ref(v___x_549_);
v_set_551_ = lean_ctor_get(v_snd_550_, 0);
v_order_552_ = lean_ctor_get(v_snd_550_, 1);
v___x_553_ = l_Lean_IR_Decl_name(v_head_547_);
lean_dec(v_head_547_);
v___x_554_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_553_, v_set_551_);
if (v___x_554_ == 0)
{
lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_565_; 
lean_inc_ref(v_order_552_);
lean_inc(v_set_551_);
v_isSharedCheck_565_ = !lean_is_exclusive(v_snd_550_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_566_ = lean_ctor_get(v_snd_550_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_snd_550_, 0);
lean_dec(v_unused_567_);
v___x_556_ = v_snd_550_;
v_isShared_557_ = v_isSharedCheck_565_;
goto v_resetjp_555_;
}
else
{
lean_dec(v_snd_550_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_565_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_558_ = lean_box(0);
lean_inc(v___x_553_);
v___x_559_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_553_, v___x_558_, v_set_551_);
v___x_560_ = lean_array_push(v_order_552_, v___x_553_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_560_);
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_562_ = v___x_556_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v_as_542_ = v_tail_548_;
v___y_544_ = v___x_562_;
goto _start;
}
}
}
else
{
lean_dec(v___x_553_);
v_as_542_ = v_tail_548_;
v___y_544_ = v_snd_550_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object* v_as_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_as_569_, v___y_570_, v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_573_, v_a_574_, v_a_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object* v_decls_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_577_, v_a_578_, v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_580_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_584_ = l_Lean_NameSet_empty;
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_586_, lean_object* v_decls_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_snd_590_; lean_object* v_order_591_; 
v___x_588_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_589_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_587_, v_env_586_, v___x_588_);
v_snd_590_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_snd_590_);
lean_dec_ref(v___x_589_);
v_order_591_ = lean_ctor_get(v_snd_590_, 1);
lean_inc_ref(v_order_591_);
lean_dec(v_snd_590_);
return v_order_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object* v_env_592_, lean_object* v_decls_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_IR_collectUsedDecls(v_env_592_, v_decls_593_);
lean_dec_ref(v_env_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_597_, lean_object* v_t_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_fst_600_ = lean_ctor_get(v_x_599_, 0);
v_snd_601_ = lean_ctor_get(v_x_599_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_599_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_x_599_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snd_601_);
lean_inc(v_fst_600_);
lean_dec(v_x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_605_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_606_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_605_, v___x_606_, v_fst_600_, v_x_597_, v_t_598_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_607_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_snd_601_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
return v_x_612_;
}
else
{
lean_object* v_key_614_; lean_object* v_value_615_; lean_object* v_tail_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_639_; 
v_key_614_ = lean_ctor_get(v_x_613_, 0);
v_value_615_ = lean_ctor_get(v_x_613_, 1);
v_tail_616_ = lean_ctor_get(v_x_613_, 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_639_ == 0)
{
v___x_618_ = v_x_613_;
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_tail_616_);
lean_inc(v_value_615_);
lean_inc(v_key_614_);
lean_dec(v_x_613_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_639_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; uint64_t v___x_621_; uint64_t v___x_622_; uint64_t v___x_623_; uint64_t v_fold_624_; uint64_t v___x_625_; uint64_t v___x_626_; uint64_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_620_ = lean_array_get_size(v_x_612_);
v___x_621_ = l_Lean_IR_instHashableVarId_hash(v_key_614_);
v___x_622_ = 32ULL;
v___x_623_ = lean_uint64_shift_right(v___x_621_, v___x_622_);
v_fold_624_ = lean_uint64_xor(v___x_621_, v___x_623_);
v___x_625_ = 16ULL;
v___x_626_ = lean_uint64_shift_right(v_fold_624_, v___x_625_);
v___x_627_ = lean_uint64_xor(v_fold_624_, v___x_626_);
v___x_628_ = lean_uint64_to_usize(v___x_627_);
v___x_629_ = lean_usize_of_nat(v___x_620_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_sub(v___x_629_, v___x_630_);
v___x_632_ = lean_usize_land(v___x_628_, v___x_631_);
v___x_633_ = lean_array_uget_borrowed(v_x_612_, v___x_632_);
lean_inc(v___x_633_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 2, v___x_633_);
v___x_635_ = v___x_618_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_key_614_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_value_615_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v___x_633_);
v___x_635_ = v_reuseFailAlloc_638_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; 
v___x_636_ = lean_array_uset(v_x_612_, v___x_632_, v___x_635_);
v_x_612_ = v___x_636_;
v_x_613_ = v_tail_616_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_640_, lean_object* v_source_641_, lean_object* v_target_642_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_array_get_size(v_source_641_);
v___x_644_ = lean_nat_dec_lt(v_i_640_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_source_641_);
lean_dec(v_i_640_);
return v_target_642_;
}
else
{
lean_object* v_es_645_; lean_object* v___x_646_; lean_object* v_source_647_; lean_object* v_target_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_es_645_ = lean_array_fget(v_source_641_, v_i_640_);
v___x_646_ = lean_box(0);
v_source_647_ = lean_array_fset(v_source_641_, v_i_640_, v___x_646_);
v_target_648_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_642_, v_es_645_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_i_640_, v___x_649_);
lean_dec(v_i_640_);
v_i_640_ = v___x_650_;
v_source_641_ = v_source_647_;
v_target_642_ = v_target_648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_nbuckets_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_653_ = lean_array_get_size(v_data_652_);
v___x_654_ = lean_unsigned_to_nat(2u);
v_nbuckets_655_ = lean_nat_mul(v___x_653_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_box(0);
v___x_658_ = lean_mk_array(v_nbuckets_655_, v___x_657_);
v___x_659_ = lean_array_propagate_mark(v_data_652_, v___x_658_);
v___x_660_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_656_, v_data_652_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
uint8_t v___x_663_; 
v___x_663_ = 0;
return v___x_663_;
}
else
{
lean_object* v_key_664_; lean_object* v_tail_665_; uint8_t v___x_666_; 
v_key_664_ = lean_ctor_get(v_x_662_, 0);
v_tail_665_ = lean_ctor_get(v_x_662_, 2);
v___x_666_ = l_Lean_IR_instBEqVarId_beq(v_key_664_, v_a_661_);
if (v___x_666_ == 0)
{
v_x_662_ = v_tail_665_;
goto _start;
}
else
{
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_668_, v_x_669_);
lean_dec(v_x_669_);
lean_dec(v_a_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_672_, lean_object* v_b_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_674_) == 0)
{
lean_dec(v_b_673_);
lean_dec(v_a_672_);
return v_x_674_;
}
else
{
lean_object* v_key_675_; lean_object* v_value_676_; lean_object* v_tail_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_689_; 
v_key_675_ = lean_ctor_get(v_x_674_, 0);
v_value_676_ = lean_ctor_get(v_x_674_, 1);
v_tail_677_ = lean_ctor_get(v_x_674_, 2);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_674_);
if (v_isSharedCheck_689_ == 0)
{
v___x_679_ = v_x_674_;
v_isShared_680_ = v_isSharedCheck_689_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_tail_677_);
lean_inc(v_value_676_);
lean_inc(v_key_675_);
lean_dec(v_x_674_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_689_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
uint8_t v___x_681_; 
v___x_681_ = l_Lean_IR_instBEqVarId_beq(v_key_675_, v_a_672_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_672_, v_b_673_, v_tail_677_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 2, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_key_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_value_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v___x_687_; 
lean_dec(v_value_676_);
lean_dec(v_key_675_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v_b_673_);
lean_ctor_set(v___x_679_, 0, v_a_672_);
v___x_687_ = v___x_679_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_672_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_b_673_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_tail_677_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_690_, lean_object* v_a_691_, lean_object* v_b_692_){
_start:
{
lean_object* v_size_693_; lean_object* v_buckets_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_737_; 
v_size_693_ = lean_ctor_get(v_m_690_, 0);
v_buckets_694_ = lean_ctor_get(v_m_690_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_m_690_);
if (v_isSharedCheck_737_ == 0)
{
v___x_696_ = v_m_690_;
v_isShared_697_ = v_isSharedCheck_737_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_buckets_694_);
lean_inc(v_size_693_);
lean_dec(v_m_690_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_737_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v_fold_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; size_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; lean_object* v_bkt_711_; uint8_t v___x_712_; 
v___x_698_ = lean_array_get_size(v_buckets_694_);
v___x_699_ = l_Lean_IR_instHashableVarId_hash(v_a_691_);
v___x_700_ = 32ULL;
v___x_701_ = lean_uint64_shift_right(v___x_699_, v___x_700_);
v_fold_702_ = lean_uint64_xor(v___x_699_, v___x_701_);
v___x_703_ = 16ULL;
v___x_704_ = lean_uint64_shift_right(v_fold_702_, v___x_703_);
v___x_705_ = lean_uint64_xor(v_fold_702_, v___x_704_);
v___x_706_ = lean_uint64_to_usize(v___x_705_);
v___x_707_ = lean_usize_of_nat(v___x_698_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_sub(v___x_707_, v___x_708_);
v___x_710_ = lean_usize_land(v___x_706_, v___x_709_);
v_bkt_711_ = lean_array_uget_borrowed(v_buckets_694_, v___x_710_);
v___x_712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_691_, v_bkt_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v_size_x27_714_; lean_object* v___x_715_; lean_object* v_buckets_x27_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v_size_x27_714_ = lean_nat_add(v_size_693_, v___x_713_);
lean_dec(v_size_693_);
lean_inc(v_bkt_711_);
v___x_715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_715_, 0, v_a_691_);
lean_ctor_set(v___x_715_, 1, v_b_692_);
lean_ctor_set(v___x_715_, 2, v_bkt_711_);
v_buckets_x27_716_ = lean_array_uset(v_buckets_694_, v___x_710_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(4u);
v___x_718_ = lean_nat_mul(v_size_x27_714_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(3u);
v___x_720_ = lean_nat_div(v___x_718_, v___x_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_array_get_size(v_buckets_x27_716_);
v___x_722_ = lean_nat_dec_le(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
if (v___x_722_ == 0)
{
lean_object* v_val_723_; lean_object* v___x_725_; 
v_val_723_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_716_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_val_723_);
lean_ctor_set(v___x_696_, 0, v_size_x27_714_);
v___x_725_ = v___x_696_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_size_x27_714_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_val_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v___x_728_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_buckets_x27_716_);
lean_ctor_set(v___x_696_, 0, v_size_x27_714_);
v___x_728_ = v___x_696_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_size_x27_714_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_buckets_x27_716_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v___x_730_; lean_object* v_buckets_x27_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
lean_inc(v_bkt_711_);
v___x_730_ = lean_box(0);
v_buckets_x27_731_ = lean_array_uset(v_buckets_694_, v___x_710_, v___x_730_);
v___x_732_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_691_, v_b_692_, v_bkt_711_);
v___x_733_ = lean_array_uset(v_buckets_x27_731_, v___x_710_, v___x_732_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_733_);
v___x_735_ = v___x_696_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_size_693_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, lean_object* v_b_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_742_ == 0)
{
lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_758_; 
v_fst_743_ = lean_ctor_get(v_b_741_, 0);
v_snd_744_ = lean_ctor_get(v_b_741_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_b_741_);
if (v_isSharedCheck_758_ == 0)
{
v___x_746_ = v_b_741_;
v_isShared_747_ = v_isSharedCheck_758_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_inc(v_fst_743_);
lean_dec(v_b_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_758_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v_x_749_; lean_object* v_ty_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_748_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v_x_749_ = lean_ctor_get(v___x_748_, 0);
v_ty_750_ = lean_ctor_get(v___x_748_, 1);
lean_inc(v_ty_750_);
lean_inc(v_x_749_);
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_743_, v_x_749_, v_ty_750_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_751_);
v___x_753_ = v___x_746_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_744_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
size_t v___x_754_; size_t v___x_755_; 
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_739_, v___x_754_);
v_i_739_ = v___x_755_;
v_b_741_ = v___x_753_;
goto _start;
}
}
}
else
{
return v_b_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_759_, lean_object* v_i_760_, lean_object* v_stop_761_, lean_object* v_b_762_){
_start:
{
size_t v_i_boxed_763_; size_t v_stop_boxed_764_; lean_object* v_res_765_; 
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_stop_boxed_764_ = lean_unbox_usize(v_stop_761_);
lean_dec(v_stop_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_759_, v_i_boxed_763_, v_stop_boxed_764_, v_b_762_);
lean_dec_ref(v_as_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_766_, lean_object* v_s_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_ps_766_);
v___x_770_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
return v_s_767_;
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_of_nat(v___x_769_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_766_, v___x_771_, v___x_772_, v_s_767_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_774_, lean_object* v_s_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_IR_CollectMaps_collectParams(v_ps_774_, v_s_775_);
lean_dec_ref(v_ps_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_777_, lean_object* v_m_778_, lean_object* v_a_779_, lean_object* v_b_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_778_, v_a_779_, v_b_780_);
return v___x_781_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_782_, lean_object* v_a_783_, lean_object* v_x_784_){
_start:
{
uint8_t v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_786_, lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
uint8_t v_res_789_; lean_object* v_r_790_; 
v_res_789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_786_, v_a_787_, v_x_788_);
lean_dec(v_x_788_);
lean_dec(v_a_787_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_791_, lean_object* v_data_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_794_, lean_object* v_a_795_, lean_object* v_b_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_795_, v_b_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_799_, lean_object* v_i_800_, lean_object* v_source_801_, lean_object* v_target_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_800_, v_source_801_, v_target_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_810_, lean_object* v_xs_811_, lean_object* v_x_812_){
_start:
{
lean_object* v_fst_813_; lean_object* v_snd_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_824_; 
v_fst_813_ = lean_ctor_get(v_x_812_, 0);
v_snd_814_ = lean_ctor_get(v_x_812_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_812_);
if (v_isSharedCheck_824_ == 0)
{
v___x_816_ = v_x_812_;
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_snd_814_);
lean_inc(v_fst_813_);
lean_dec(v_x_812_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_818_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_819_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_818_, v___x_819_, v_snd_814_, v_j_810_, v_xs_811_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_fst_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
if (lean_obj_tag(v_x_826_) == 0)
{
uint8_t v___x_827_; 
v___x_827_ = 0;
return v___x_827_;
}
else
{
lean_object* v_key_828_; lean_object* v_tail_829_; uint8_t v___x_830_; 
v_key_828_ = lean_ctor_get(v_x_826_, 0);
v_tail_829_ = lean_ctor_get(v_x_826_, 2);
v___x_830_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_828_, v_a_825_);
if (v___x_830_ == 0)
{
v_x_826_ = v_tail_829_;
goto _start;
}
else
{
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_832_, lean_object* v_x_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_832_, v_x_833_);
lean_dec(v_x_833_);
lean_dec(v_a_832_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
if (lean_obj_tag(v_x_837_) == 0)
{
return v_x_836_;
}
else
{
lean_object* v_key_838_; lean_object* v_value_839_; lean_object* v_tail_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_863_; 
v_key_838_ = lean_ctor_get(v_x_837_, 0);
v_value_839_ = lean_ctor_get(v_x_837_, 1);
v_tail_840_ = lean_ctor_get(v_x_837_, 2);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_837_);
if (v_isSharedCheck_863_ == 0)
{
v___x_842_ = v_x_837_;
v_isShared_843_ = v_isSharedCheck_863_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_tail_840_);
lean_inc(v_value_839_);
lean_inc(v_key_838_);
lean_dec(v_x_837_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_863_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; uint64_t v___x_845_; uint64_t v___x_846_; uint64_t v___x_847_; uint64_t v_fold_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_844_ = lean_array_get_size(v_x_836_);
v___x_845_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_838_);
v___x_846_ = 32ULL;
v___x_847_ = lean_uint64_shift_right(v___x_845_, v___x_846_);
v_fold_848_ = lean_uint64_xor(v___x_845_, v___x_847_);
v___x_849_ = 16ULL;
v___x_850_ = lean_uint64_shift_right(v_fold_848_, v___x_849_);
v___x_851_ = lean_uint64_xor(v_fold_848_, v___x_850_);
v___x_852_ = lean_uint64_to_usize(v___x_851_);
v___x_853_ = lean_usize_of_nat(v___x_844_);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_sub(v___x_853_, v___x_854_);
v___x_856_ = lean_usize_land(v___x_852_, v___x_855_);
v___x_857_ = lean_array_uget_borrowed(v_x_836_, v___x_856_);
lean_inc(v___x_857_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 2, v___x_857_);
v___x_859_ = v___x_842_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_key_838_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_value_839_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v___x_857_);
v___x_859_ = v_reuseFailAlloc_862_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = lean_array_uset(v_x_836_, v___x_856_, v___x_859_);
v_x_836_ = v___x_860_;
v_x_837_ = v_tail_840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_864_, lean_object* v_source_865_, lean_object* v_target_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_array_get_size(v_source_865_);
v___x_868_ = lean_nat_dec_lt(v_i_864_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec_ref(v_source_865_);
lean_dec(v_i_864_);
return v_target_866_;
}
else
{
lean_object* v_es_869_; lean_object* v___x_870_; lean_object* v_source_871_; lean_object* v_target_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_es_869_ = lean_array_fget(v_source_865_, v_i_864_);
v___x_870_ = lean_box(0);
v_source_871_ = lean_array_fset(v_source_865_, v_i_864_, v___x_870_);
v_target_872_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_866_, v_es_869_);
v___x_873_ = lean_unsigned_to_nat(1u);
v___x_874_ = lean_nat_add(v_i_864_, v___x_873_);
lean_dec(v_i_864_);
v_i_864_ = v___x_874_;
v_source_865_ = v_source_871_;
v_target_866_ = v_target_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_nbuckets_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_877_ = lean_array_get_size(v_data_876_);
v___x_878_ = lean_unsigned_to_nat(2u);
v_nbuckets_879_ = lean_nat_mul(v___x_877_, v___x_878_);
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_box(0);
v___x_882_ = lean_mk_array(v_nbuckets_879_, v___x_881_);
v___x_883_ = lean_array_propagate_mark(v_data_876_, v___x_882_);
v___x_884_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_880_, v_data_876_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_885_, lean_object* v_b_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_dec(v_b_886_);
lean_dec(v_a_885_);
return v_x_887_;
}
else
{
lean_object* v_key_888_; lean_object* v_value_889_; lean_object* v_tail_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_902_; 
v_key_888_ = lean_ctor_get(v_x_887_, 0);
v_value_889_ = lean_ctor_get(v_x_887_, 1);
v_tail_890_ = lean_ctor_get(v_x_887_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_902_ == 0)
{
v___x_892_ = v_x_887_;
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_tail_890_);
lean_inc(v_value_889_);
lean_inc(v_key_888_);
lean_dec(v_x_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_888_, v_a_885_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_885_, v_b_886_, v_tail_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v___x_895_);
v___x_897_ = v___x_892_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_key_888_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_value_889_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v___x_900_; 
lean_dec(v_value_889_);
lean_dec(v_key_888_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_b_886_);
lean_ctor_set(v___x_892_, 0, v_a_885_);
v___x_900_ = v___x_892_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_b_886_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_tail_890_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_903_, lean_object* v_a_904_, lean_object* v_b_905_){
_start:
{
lean_object* v_size_906_; lean_object* v_buckets_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_950_; 
v_size_906_ = lean_ctor_get(v_m_903_, 0);
v_buckets_907_ = lean_ctor_get(v_m_903_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_m_903_);
if (v_isSharedCheck_950_ == 0)
{
v___x_909_ = v_m_903_;
v_isShared_910_ = v_isSharedCheck_950_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_buckets_907_);
lean_inc(v_size_906_);
lean_dec(v_m_903_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_950_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v___x_914_; uint64_t v_fold_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v_bkt_924_; uint8_t v___x_925_; 
v___x_911_ = lean_array_get_size(v_buckets_907_);
v___x_912_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_904_);
v___x_913_ = 32ULL;
v___x_914_ = lean_uint64_shift_right(v___x_912_, v___x_913_);
v_fold_915_ = lean_uint64_xor(v___x_912_, v___x_914_);
v___x_916_ = 16ULL;
v___x_917_ = lean_uint64_shift_right(v_fold_915_, v___x_916_);
v___x_918_ = lean_uint64_xor(v_fold_915_, v___x_917_);
v___x_919_ = lean_uint64_to_usize(v___x_918_);
v___x_920_ = lean_usize_of_nat(v___x_911_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_sub(v___x_920_, v___x_921_);
v___x_923_ = lean_usize_land(v___x_919_, v___x_922_);
v_bkt_924_ = lean_array_uget_borrowed(v_buckets_907_, v___x_923_);
v___x_925_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_904_, v_bkt_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v_size_x27_927_; lean_object* v___x_928_; lean_object* v_buckets_x27_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v_size_x27_927_ = lean_nat_add(v_size_906_, v___x_926_);
lean_dec(v_size_906_);
lean_inc(v_bkt_924_);
v___x_928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_928_, 0, v_a_904_);
lean_ctor_set(v___x_928_, 1, v_b_905_);
lean_ctor_set(v___x_928_, 2, v_bkt_924_);
v_buckets_x27_929_ = lean_array_uset(v_buckets_907_, v___x_923_, v___x_928_);
v___x_930_ = lean_unsigned_to_nat(4u);
v___x_931_ = lean_nat_mul(v_size_x27_927_, v___x_930_);
v___x_932_ = lean_unsigned_to_nat(3u);
v___x_933_ = lean_nat_div(v___x_931_, v___x_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_array_get_size(v_buckets_x27_929_);
v___x_935_ = lean_nat_dec_le(v___x_933_, v___x_934_);
lean_dec(v___x_933_);
if (v___x_935_ == 0)
{
lean_object* v_val_936_; lean_object* v___x_938_; 
v_val_936_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_929_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_val_936_);
lean_ctor_set(v___x_909_, 0, v_size_x27_927_);
v___x_938_ = v___x_909_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_size_x27_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_val_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_941_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v_buckets_x27_929_);
lean_ctor_set(v___x_909_, 0, v_size_x27_927_);
v___x_941_ = v___x_909_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_size_x27_927_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_buckets_x27_929_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v___x_943_; lean_object* v_buckets_x27_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc(v_bkt_924_);
v___x_943_ = lean_box(0);
v_buckets_x27_944_ = lean_array_uset(v_buckets_907_, v___x_923_, v___x_943_);
v___x_945_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_904_, v_b_905_, v_bkt_924_);
v___x_946_ = lean_array_uset(v_buckets_x27_944_, v___x_923_, v___x_945_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_946_);
v___x_948_ = v___x_909_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_size_906_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_951_, lean_object* v_a_952_){
_start:
{
switch(lean_obj_tag(v_x_951_))
{
case 0:
{
lean_object* v_x_953_; lean_object* v_ty_954_; lean_object* v_b_955_; lean_object* v___x_956_; lean_object* v_fst_957_; lean_object* v_snd_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_x_953_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_x_953_);
v_ty_954_ = lean_ctor_get(v_x_951_, 1);
lean_inc(v_ty_954_);
v_b_955_ = lean_ctor_get(v_x_951_, 3);
lean_inc(v_b_955_);
lean_dec_ref_known(v_x_951_, 4);
v___x_956_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_955_, v_a_952_);
v_fst_957_ = lean_ctor_get(v___x_956_, 0);
v_snd_958_ = lean_ctor_get(v___x_956_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_956_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snd_958_);
lean_inc(v_fst_957_);
lean_dec(v___x_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_957_, v_x_953_, v_ty_954_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_snd_958_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
case 1:
{
lean_object* v_j_967_; lean_object* v_xs_968_; lean_object* v_v_969_; lean_object* v_b_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_fst_974_; lean_object* v_snd_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_983_; 
v_j_967_ = lean_ctor_get(v_x_951_, 0);
lean_inc(v_j_967_);
v_xs_968_ = lean_ctor_get(v_x_951_, 1);
lean_inc_ref(v_xs_968_);
v_v_969_ = lean_ctor_get(v_x_951_, 2);
lean_inc(v_v_969_);
v_b_970_ = lean_ctor_get(v_x_951_, 3);
lean_inc(v_b_970_);
lean_dec_ref_known(v_x_951_, 4);
v___x_971_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_970_, v_a_952_);
v___x_972_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_969_, v___x_971_);
v___x_973_ = l_Lean_IR_CollectMaps_collectParams(v_xs_968_, v___x_972_);
v_fst_974_ = lean_ctor_get(v___x_973_, 0);
v_snd_975_ = lean_ctor_get(v___x_973_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_983_ == 0)
{
v___x_977_ = v___x_973_;
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_snd_975_);
lean_inc(v_fst_974_);
lean_dec(v___x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_975_, v_j_967_, v_xs_968_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v___x_979_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_fst_974_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
case 9:
{
lean_object* v_cs_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_cs_984_ = lean_ctor_get(v_x_951_, 3);
lean_inc_ref(v_cs_984_);
lean_dec_ref_known(v_x_951_, 4);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_array_get_size(v_cs_984_);
v___x_987_ = lean_nat_dec_lt(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v_cs_984_);
return v_a_952_;
}
else
{
size_t v___x_988_; size_t v___x_989_; lean_object* v___x_990_; 
v___x_988_ = ((size_t)0ULL);
v___x_989_ = lean_usize_of_nat(v___x_986_);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_984_, v___x_988_, v___x_989_, v_a_952_);
lean_dec_ref(v_cs_984_);
return v___x_990_;
}
}
default: 
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_IR_FnBody_isTerminal(v_x_951_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_IR_FnBody_body(v_x_951_);
lean_dec(v_x_951_);
v_x_951_ = v___x_992_;
goto _start;
}
else
{
lean_dec(v_x_951_);
return v_a_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_994_, size_t v_i_995_, size_t v_stop_996_, lean_object* v_b_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = lean_usize_dec_eq(v_i_995_, v_stop_996_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; 
v___x_999_ = lean_array_uget_borrowed(v_as_994_, v_i_995_);
v___x_1000_ = l_Lean_IR_Alt_body(v___x_999_);
v___x_1001_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1000_, v_b_997_);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_995_, v___x_1002_);
v_i_995_ = v___x_1003_;
v_b_997_ = v___x_1001_;
goto _start;
}
else
{
return v_b_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1005_, lean_object* v_i_1006_, lean_object* v_stop_1007_, lean_object* v_b_1008_){
_start:
{
size_t v_i_boxed_1009_; size_t v_stop_boxed_1010_; lean_object* v_res_1011_; 
v_i_boxed_1009_ = lean_unbox_usize(v_i_1006_);
lean_dec(v_i_1006_);
v_stop_boxed_1010_ = lean_unbox_usize(v_stop_1007_);
lean_dec(v_stop_1007_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1005_, v_i_boxed_1009_, v_stop_boxed_1010_, v_b_1008_);
lean_dec_ref(v_as_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1012_, lean_object* v_m_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1013_, v_a_1014_, v_b_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1017_, lean_object* v_a_1018_, lean_object* v_x_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1018_, v_x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_a_1022_, lean_object* v_x_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1021_, v_a_1022_, v_x_1023_);
lean_dec(v_x_1023_);
lean_dec(v_a_1022_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1026_, lean_object* v_data_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1030_, v_b_1031_, v_x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1034_, lean_object* v_i_1035_, lean_object* v_source_1036_, lean_object* v_target_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1035_, v_source_1036_, v_target_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1043_, lean_object* v_a_1044_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v_xs_1045_; lean_object* v_body_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_xs_1045_ = lean_ctor_get(v_x_1043_, 1);
lean_inc_ref(v_xs_1045_);
v_body_1046_ = lean_ctor_get(v_x_1043_, 3);
lean_inc(v_body_1046_);
lean_dec_ref_known(v_x_1043_, 5);
v___x_1047_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1046_, v_a_1044_);
v___x_1048_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1045_, v___x_1047_);
lean_dec_ref(v_xs_1045_);
return v___x_1048_;
}
else
{
lean_dec_ref(v_x_1043_);
return v_a_1044_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_unsigned_to_nat(16u);
v___x_1051_ = lean_mk_array(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1059_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1057_, v___x_1058_);
return v___x_1059_;
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
