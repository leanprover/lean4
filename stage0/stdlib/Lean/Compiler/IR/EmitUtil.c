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
uint8_t l_Lean_IR_FnBody_isVarDecl(lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_FnBody_targetVar(lean_object*);
lean_object* l_Lean_IR_FnBody_targetType(lean_object*);
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
if (lean_obj_tag(v_b_2_) == 6)
{
lean_object* v_b_3_; 
v_b_3_ = lean_ctor_get(v_b_2_, 1);
if (lean_obj_tag(v_b_3_) == 28)
{
lean_object* v_x_4_; 
v_x_4_ = lean_ctor_get(v_b_3_, 0);
if (lean_obj_tag(v_x_4_) == 0)
{
lean_object* v_tgt_5_; lean_object* v_c_6_; lean_object* v_id_7_; uint8_t v___x_8_; 
v_tgt_5_ = lean_ctor_get(v_b_2_, 0);
v_c_6_ = lean_ctor_get(v_b_2_, 3);
v_id_7_ = lean_ctor_get(v_x_4_, 0);
v___x_8_ = l_Lean_IR_instBEqVarId_beq(v_tgt_5_, v_id_7_);
if (v___x_8_ == 0)
{
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = lean_name_eq(v_c_6_, v_g_1_);
return v___x_9_;
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
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
}
LEAN_EXPORT lean_object* l_Lean_IR_isTailCallTo___boxed(lean_object* v_g_13_, lean_object* v_b_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_IR_isTailCallTo(v_g_13_, v_b_14_);
lean_dec(v_b_14_);
lean_dec(v_g_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(lean_object* v_modulePrefix_17_, lean_object* v_as_18_, size_t v_i_19_, size_t v_stop_20_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = lean_usize_dec_eq(v_i_19_, v_stop_20_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v_toImport_27_; uint8_t v_irPhases_28_; uint8_t v___x_29_; uint8_t v___x_30_; 
v___x_26_ = lean_array_uget_borrowed(v_as_18_, v_i_19_);
v_toImport_27_ = lean_ctor_get(v___x_26_, 0);
v_irPhases_28_ = lean_ctor_get_uint8(v___x_26_, sizeof(void*)*1);
v___x_29_ = 1;
v___x_30_ = l_Lean_instBEqIRPhases_beq(v_irPhases_28_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v_module_31_; uint8_t v___x_32_; 
v_module_31_ = lean_ctor_get(v_toImport_27_, 0);
v___x_32_ = l_Lean_Name_isPrefixOf(v_modulePrefix_17_, v_module_31_);
if (v___x_32_ == 0)
{
goto v___jp_21_;
}
else
{
return v___x_32_;
}
}
else
{
goto v___jp_21_;
}
}
else
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
v___jp_21_:
{
size_t v___x_22_; size_t v___x_23_; 
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_add(v_i_19_, v___x_22_);
v_i_19_ = v___x_23_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_34_, lean_object* v_as_35_, lean_object* v_i_36_, lean_object* v_stop_37_){
_start:
{
size_t v_i_boxed_38_; size_t v_stop_boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v_i_boxed_38_ = lean_unbox_usize(v_i_36_);
lean_dec(v_i_36_);
v_stop_boxed_39_ = lean_unbox_usize(v_stop_37_);
lean_dec(v_stop_37_);
v_res_40_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_34_, v_as_35_, v_i_boxed_38_, v_stop_boxed_39_);
lean_dec_ref(v_as_35_);
lean_dec(v_modulePrefix_34_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_usesModuleFrom(lean_object* v_env_42_, lean_object* v_modulePrefix_43_){
_start:
{
lean_object* v___x_44_; lean_object* v_modules_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_44_ = l_Lean_Environment_header(v_env_42_);
v_modules_45_ = lean_ctor_get(v___x_44_, 3);
lean_inc_ref(v_modules_45_);
lean_dec_ref(v___x_44_);
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_array_get_size(v_modules_45_);
v___x_48_ = lean_nat_dec_lt(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
lean_dec_ref(v_modules_45_);
return v___x_48_;
}
else
{
if (v___x_48_ == 0)
{
lean_dec_ref(v_modules_45_);
return v___x_48_;
}
else
{
size_t v___x_49_; size_t v___x_50_; uint8_t v___x_51_; 
v___x_49_ = ((size_t)0ULL);
v___x_50_ = lean_usize_of_nat(v___x_47_);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_usesModuleFrom_spec__0(v_modulePrefix_43_, v_modules_45_, v___x_49_, v___x_50_);
lean_dec_ref(v_modules_45_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_usesModuleFrom___boxed(lean_object* v_env_52_, lean_object* v_modulePrefix_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Lean_IR_usesModuleFrom(v_env_52_, v_modulePrefix_53_);
lean_dec(v_modulePrefix_53_);
lean_dec_ref(v_env_52_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___redArg(lean_object* v_f_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_set_59_; lean_object* v_order_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_set_59_ = lean_ctor_get(v_a_58_, 0);
v_order_60_ = lean_ctor_get(v_a_58_, 1);
v___x_61_ = lean_box(0);
v___x_62_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_59_);
lean_inc(v_f_57_);
v___x_63_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_62_, v_f_57_, v_set_59_);
if (v___x_63_ == 0)
{
lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_73_; 
lean_inc_ref(v_order_60_);
lean_inc(v_set_59_);
v_isSharedCheck_73_ = !lean_is_exclusive(v_a_58_);
if (v_isSharedCheck_73_ == 0)
{
lean_object* v_unused_74_; lean_object* v_unused_75_; 
v_unused_74_ = lean_ctor_get(v_a_58_, 1);
lean_dec(v_unused_74_);
v_unused_75_ = lean_ctor_get(v_a_58_, 0);
lean_dec(v_unused_75_);
v___x_65_ = v_a_58_;
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
else
{
lean_dec(v_a_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
lean_inc(v_f_57_);
v___x_67_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_62_, v_f_57_, v___x_61_, v_set_59_);
v___x_68_ = lean_array_push(v_order_60_, v_f_57_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_68_);
lean_ctor_set(v___x_65_, 0, v___x_67_);
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_67_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_61_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
return v___x_71_;
}
}
}
else
{
lean_object* v___x_76_; 
lean_dec(v_f_57_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_61_);
lean_ctor_set(v___x_76_, 1, v_a_58_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* v_f_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_set_80_; lean_object* v_order_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_set_80_ = lean_ctor_get(v_a_79_, 0);
v_order_81_ = lean_ctor_get(v_a_79_, 1);
v___x_82_ = lean_box(0);
v___x_83_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_80_);
lean_inc(v_f_77_);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_83_, v_f_77_, v_set_80_);
if (v___x_84_ == 0)
{
lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_94_; 
lean_inc_ref(v_order_81_);
lean_inc(v_set_80_);
v_isSharedCheck_94_ = !lean_is_exclusive(v_a_79_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; 
v_unused_95_ = lean_ctor_get(v_a_79_, 1);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_a_79_, 0);
lean_dec(v_unused_96_);
v___x_86_ = v_a_79_;
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
else
{
lean_dec(v_a_79_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_94_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
lean_inc(v_f_77_);
v___x_88_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_83_, v_f_77_, v___x_82_, v_set_80_);
v___x_89_ = lean_array_push(v_order_81_, v_f_77_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___x_89_);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_93_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_82_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
return v___x_92_;
}
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_f_77_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_82_);
lean_ctor_set(v___x_97_, 1, v_a_79_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* v_f_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_IR_CollectUsedDecls_collect(v_f_98_, v_a_99_, v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object* v_k_102_, lean_object* v_v_103_, lean_object* v_t_104_){
_start:
{
if (lean_obj_tag(v_t_104_) == 0)
{
lean_object* v_size_105_; lean_object* v_k_106_; lean_object* v_v_107_; lean_object* v_l_108_; lean_object* v_r_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_389_; 
v_size_105_ = lean_ctor_get(v_t_104_, 0);
v_k_106_ = lean_ctor_get(v_t_104_, 1);
v_v_107_ = lean_ctor_get(v_t_104_, 2);
v_l_108_ = lean_ctor_get(v_t_104_, 3);
v_r_109_ = lean_ctor_get(v_t_104_, 4);
v_isSharedCheck_389_ = !lean_is_exclusive(v_t_104_);
if (v_isSharedCheck_389_ == 0)
{
v___x_111_ = v_t_104_;
v_isShared_112_ = v_isSharedCheck_389_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_r_109_);
lean_inc(v_l_108_);
lean_inc(v_v_107_);
lean_inc(v_k_106_);
lean_inc(v_size_105_);
lean_dec(v_t_104_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_389_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
uint8_t v___x_113_; 
v___x_113_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_102_, v_k_106_);
switch(v___x_113_)
{
case 0:
{
lean_object* v_impl_114_; lean_object* v___x_115_; 
lean_dec(v_size_105_);
v_impl_114_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_102_, v_v_103_, v_l_108_);
v___x_115_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_109_) == 0)
{
lean_object* v_size_116_; lean_object* v_size_117_; lean_object* v_k_118_; lean_object* v_v_119_; lean_object* v_l_120_; lean_object* v_r_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_size_116_ = lean_ctor_get(v_r_109_, 0);
v_size_117_ = lean_ctor_get(v_impl_114_, 0);
v_k_118_ = lean_ctor_get(v_impl_114_, 1);
v_v_119_ = lean_ctor_get(v_impl_114_, 2);
v_l_120_ = lean_ctor_get(v_impl_114_, 3);
v_r_121_ = lean_ctor_get(v_impl_114_, 4);
lean_inc(v_r_121_);
v___x_122_ = lean_unsigned_to_nat(3u);
v___x_123_ = lean_nat_mul(v___x_122_, v_size_116_);
v___x_124_ = lean_nat_dec_lt(v___x_123_, v_size_117_);
lean_dec(v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_r_121_);
v___x_125_ = lean_nat_add(v___x_115_, v_size_117_);
v___x_126_ = lean_nat_add(v___x_125_, v_size_116_);
lean_dec(v___x_125_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 3, v_impl_114_);
lean_ctor_set(v___x_111_, 0, v___x_126_);
v___x_128_ = v___x_111_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_impl_114_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_r_109_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_195_; 
lean_inc(v_l_120_);
lean_inc(v_v_119_);
lean_inc(v_k_118_);
lean_inc(v_size_117_);
v_isSharedCheck_195_ = !lean_is_exclusive(v_impl_114_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; lean_object* v_unused_197_; lean_object* v_unused_198_; lean_object* v_unused_199_; lean_object* v_unused_200_; 
v_unused_196_ = lean_ctor_get(v_impl_114_, 4);
lean_dec(v_unused_196_);
v_unused_197_ = lean_ctor_get(v_impl_114_, 3);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_impl_114_, 2);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_impl_114_, 1);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_impl_114_, 0);
lean_dec(v_unused_200_);
v___x_131_ = v_impl_114_;
v_isShared_132_ = v_isSharedCheck_195_;
goto v_resetjp_130_;
}
else
{
lean_dec(v_impl_114_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_195_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v_size_133_; lean_object* v_size_134_; lean_object* v_k_135_; lean_object* v_v_136_; lean_object* v_l_137_; lean_object* v_r_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_size_133_ = lean_ctor_get(v_l_120_, 0);
v_size_134_ = lean_ctor_get(v_r_121_, 0);
v_k_135_ = lean_ctor_get(v_r_121_, 1);
v_v_136_ = lean_ctor_get(v_r_121_, 2);
v_l_137_ = lean_ctor_get(v_r_121_, 3);
v_r_138_ = lean_ctor_get(v_r_121_, 4);
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = lean_nat_mul(v___x_139_, v_size_133_);
v___x_141_ = lean_nat_dec_lt(v_size_134_, v___x_140_);
lean_dec(v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_170_; 
lean_inc(v_r_138_);
lean_inc(v_l_137_);
lean_inc(v_v_136_);
lean_inc(v_k_135_);
v_isSharedCheck_170_ = !lean_is_exclusive(v_r_121_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; 
v_unused_171_ = lean_ctor_get(v_r_121_, 4);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_r_121_, 3);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_121_, 2);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_121_, 1);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_r_121_, 0);
lean_dec(v_unused_175_);
v___x_143_ = v_r_121_;
v_isShared_144_ = v_isSharedCheck_170_;
goto v_resetjp_142_;
}
else
{
lean_dec(v_r_121_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_170_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___x_158_; lean_object* v___y_160_; 
v___x_145_ = lean_nat_add(v___x_115_, v_size_117_);
lean_dec(v_size_117_);
v___x_146_ = lean_nat_add(v___x_145_, v_size_116_);
lean_dec(v___x_145_);
v___x_158_ = lean_nat_add(v___x_115_, v_size_133_);
if (lean_obj_tag(v_l_137_) == 0)
{
lean_object* v_size_168_; 
v_size_168_ = lean_ctor_get(v_l_137_, 0);
lean_inc(v_size_168_);
v___y_160_ = v_size_168_;
goto v___jp_159_;
}
else
{
lean_object* v___x_169_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___y_160_ = v___x_169_;
goto v___jp_159_;
}
v___jp_147_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_nat_add(v___y_148_, v___y_150_);
lean_dec(v___y_150_);
lean_dec(v___y_148_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 4, v_r_109_);
lean_ctor_set(v___x_143_, 3, v_r_138_);
lean_ctor_set(v___x_143_, 2, v_v_107_);
lean_ctor_set(v___x_143_, 1, v_k_106_);
lean_ctor_set(v___x_143_, 0, v___x_151_);
v___x_153_ = v___x_143_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_157_, 3, v_r_138_);
lean_ctor_set(v_reuseFailAlloc_157_, 4, v_r_109_);
v___x_153_ = v_reuseFailAlloc_157_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_155_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v___x_153_);
lean_ctor_set(v___x_131_, 3, v___y_149_);
lean_ctor_set(v___x_131_, 2, v_v_136_);
lean_ctor_set(v___x_131_, 1, v_k_135_);
lean_ctor_set(v___x_131_, 0, v___x_146_);
v___x_155_ = v___x_131_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_135_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_136_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v___y_149_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_nat_add(v___x_158_, v___y_160_);
lean_dec(v___y_160_);
lean_dec(v___x_158_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_l_137_);
lean_ctor_set(v___x_111_, 3, v_l_120_);
lean_ctor_set(v___x_111_, 2, v_v_119_);
lean_ctor_set(v___x_111_, 1, v_k_118_);
lean_ctor_set(v___x_111_, 0, v___x_161_);
v___x_163_ = v___x_111_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_k_118_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_v_119_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_l_120_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_l_137_);
v___x_163_ = v_reuseFailAlloc_167_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; 
v___x_164_ = lean_nat_add(v___x_115_, v_size_116_);
if (lean_obj_tag(v_r_138_) == 0)
{
lean_object* v_size_165_; 
v_size_165_ = lean_ctor_get(v_r_138_, 0);
lean_inc(v_size_165_);
v___y_148_ = v___x_164_;
v___y_149_ = v___x_163_;
v___y_150_ = v_size_165_;
goto v___jp_147_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_unsigned_to_nat(0u);
v___y_148_ = v___x_164_;
v___y_149_ = v___x_163_;
v___y_150_ = v___x_166_;
goto v___jp_147_;
}
}
}
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_del_object(v___x_111_);
v___x_176_ = lean_nat_add(v___x_115_, v_size_117_);
lean_dec(v_size_117_);
v___x_177_ = lean_nat_add(v___x_176_, v_size_116_);
lean_dec(v___x_176_);
v___x_178_ = lean_nat_add(v___x_115_, v_size_116_);
v___x_179_ = lean_nat_add(v___x_178_, v_size_134_);
lean_dec(v___x_178_);
lean_inc_ref(v_r_109_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 4, v_r_109_);
lean_ctor_set(v___x_131_, 3, v_r_121_);
lean_ctor_set(v___x_131_, 2, v_v_107_);
lean_ctor_set(v___x_131_, 1, v_k_106_);
lean_ctor_set(v___x_131_, 0, v___x_179_);
v___x_181_ = v___x_131_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_r_121_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v_r_109_);
v___x_181_ = v_reuseFailAlloc_194_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_isSharedCheck_188_ = !lean_is_exclusive(v_r_109_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; 
v_unused_189_ = lean_ctor_get(v_r_109_, 4);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_r_109_, 3);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_r_109_, 2);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_r_109_, 1);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_r_109_, 0);
lean_dec(v_unused_193_);
v___x_183_ = v_r_109_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_r_109_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___x_181_);
lean_ctor_set(v___x_183_, 3, v_l_120_);
lean_ctor_set(v___x_183_, 2, v_v_119_);
lean_ctor_set(v___x_183_, 1, v_k_118_);
lean_ctor_set(v___x_183_, 0, v___x_177_);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_k_118_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_v_119_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_l_120_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v___x_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_201_; 
v_l_201_ = lean_ctor_get(v_impl_114_, 3);
if (lean_obj_tag(v_l_201_) == 0)
{
lean_object* v_r_202_; lean_object* v_k_203_; lean_object* v_v_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_215_; 
lean_inc_ref(v_l_201_);
v_r_202_ = lean_ctor_get(v_impl_114_, 4);
v_k_203_ = lean_ctor_get(v_impl_114_, 1);
v_v_204_ = lean_ctor_get(v_impl_114_, 2);
v_isSharedCheck_215_ = !lean_is_exclusive(v_impl_114_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; lean_object* v_unused_217_; 
v_unused_216_ = lean_ctor_get(v_impl_114_, 3);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_impl_114_, 0);
lean_dec(v_unused_217_);
v___x_206_ = v_impl_114_;
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_r_202_);
lean_inc(v_v_204_);
lean_inc(v_k_203_);
lean_dec(v_impl_114_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_202_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v_r_202_);
lean_ctor_set(v___x_206_, 2, v_v_107_);
lean_ctor_set(v___x_206_, 1, v_k_106_);
lean_ctor_set(v___x_206_, 0, v___x_115_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_r_202_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_r_202_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v___x_210_);
lean_ctor_set(v___x_111_, 3, v_l_201_);
lean_ctor_set(v___x_111_, 2, v_v_204_);
lean_ctor_set(v___x_111_, 1, v_k_203_);
lean_ctor_set(v___x_111_, 0, v___x_208_);
v___x_212_ = v___x_111_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_k_203_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_v_204_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_l_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_r_218_; 
v_r_218_ = lean_ctor_get(v_impl_114_, 4);
lean_inc(v_r_218_);
if (lean_obj_tag(v_r_218_) == 0)
{
lean_object* v_k_219_; lean_object* v_v_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_243_; 
lean_inc(v_l_201_);
v_k_219_ = lean_ctor_get(v_impl_114_, 1);
v_v_220_ = lean_ctor_get(v_impl_114_, 2);
v_isSharedCheck_243_ = !lean_is_exclusive(v_impl_114_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_244_ = lean_ctor_get(v_impl_114_, 4);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_impl_114_, 3);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_impl_114_, 0);
lean_dec(v_unused_246_);
v___x_222_ = v_impl_114_;
v_isShared_223_ = v_isSharedCheck_243_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_v_220_);
lean_inc(v_k_219_);
lean_dec(v_impl_114_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_243_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_k_224_; lean_object* v_v_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_k_224_ = lean_ctor_get(v_r_218_, 1);
v_v_225_ = lean_ctor_get(v_r_218_, 2);
v_isSharedCheck_239_ = !lean_is_exclusive(v_r_218_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; lean_object* v_unused_241_; lean_object* v_unused_242_; 
v_unused_240_ = lean_ctor_get(v_r_218_, 4);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_r_218_, 3);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_r_218_, 0);
lean_dec(v_unused_242_);
v___x_227_ = v_r_218_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_v_225_);
lean_inc(v_k_224_);
lean_dec(v_r_218_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(3u);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 4, v_l_201_);
lean_ctor_set(v___x_227_, 3, v_l_201_);
lean_ctor_set(v___x_227_, 2, v_v_220_);
lean_ctor_set(v___x_227_, 1, v_k_219_);
lean_ctor_set(v___x_227_, 0, v___x_115_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_l_201_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_l_201_);
v___x_231_ = v_reuseFailAlloc_238_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_233_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 4, v_l_201_);
lean_ctor_set(v___x_222_, 2, v_v_107_);
lean_ctor_set(v___x_222_, 1, v_k_106_);
lean_ctor_set(v___x_222_, 0, v___x_115_);
v___x_233_ = v___x_222_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_l_201_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_l_201_);
v___x_233_ = v_reuseFailAlloc_237_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v___x_233_);
lean_ctor_set(v___x_111_, 3, v___x_231_);
lean_ctor_set(v___x_111_, 2, v_v_225_);
lean_ctor_set(v___x_111_, 1, v_k_224_);
lean_ctor_set(v___x_111_, 0, v___x_229_);
v___x_235_ = v___x_111_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_k_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_v_225_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(2u);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_r_218_);
lean_ctor_set(v___x_111_, 3, v_impl_114_);
lean_ctor_set(v___x_111_, 0, v___x_247_);
v___x_249_ = v___x_111_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_impl_114_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_r_218_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
case 1:
{
lean_object* v___x_252_; 
lean_dec(v_v_107_);
lean_dec(v_k_106_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 2, v_v_103_);
lean_ctor_set(v___x_111_, 1, v_k_102_);
v___x_252_ = v___x_111_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_size_105_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_k_102_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_v_103_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_253_, 4, v_r_109_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
default: 
{
lean_object* v_impl_254_; lean_object* v___x_255_; 
lean_dec(v_size_105_);
v_impl_254_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_102_, v_v_103_, v_r_109_);
v___x_255_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_108_) == 0)
{
lean_object* v_size_256_; lean_object* v_size_257_; lean_object* v_k_258_; lean_object* v_v_259_; lean_object* v_l_260_; lean_object* v_r_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_size_256_ = lean_ctor_get(v_l_108_, 0);
v_size_257_ = lean_ctor_get(v_impl_254_, 0);
v_k_258_ = lean_ctor_get(v_impl_254_, 1);
v_v_259_ = lean_ctor_get(v_impl_254_, 2);
v_l_260_ = lean_ctor_get(v_impl_254_, 3);
lean_inc(v_l_260_);
v_r_261_ = lean_ctor_get(v_impl_254_, 4);
v___x_262_ = lean_unsigned_to_nat(3u);
v___x_263_ = lean_nat_mul(v___x_262_, v_size_256_);
v___x_264_ = lean_nat_dec_lt(v___x_263_, v_size_257_);
lean_dec(v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
lean_dec(v_l_260_);
v___x_265_ = lean_nat_add(v___x_255_, v_size_256_);
v___x_266_ = lean_nat_add(v___x_265_, v_size_257_);
lean_dec(v___x_265_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_impl_254_);
lean_ctor_set(v___x_111_, 0, v___x_266_);
v___x_268_ = v___x_111_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_impl_254_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_333_; 
lean_inc(v_r_261_);
lean_inc(v_v_259_);
lean_inc(v_k_258_);
lean_inc(v_size_257_);
v_isSharedCheck_333_ = !lean_is_exclusive(v_impl_254_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; lean_object* v_unused_335_; lean_object* v_unused_336_; lean_object* v_unused_337_; lean_object* v_unused_338_; 
v_unused_334_ = lean_ctor_get(v_impl_254_, 4);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_impl_254_, 3);
lean_dec(v_unused_335_);
v_unused_336_ = lean_ctor_get(v_impl_254_, 2);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_impl_254_, 1);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_impl_254_, 0);
lean_dec(v_unused_338_);
v___x_271_ = v_impl_254_;
v_isShared_272_ = v_isSharedCheck_333_;
goto v_resetjp_270_;
}
else
{
lean_dec(v_impl_254_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_333_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v_size_273_; lean_object* v_k_274_; lean_object* v_v_275_; lean_object* v_l_276_; lean_object* v_r_277_; lean_object* v_size_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_size_273_ = lean_ctor_get(v_l_260_, 0);
v_k_274_ = lean_ctor_get(v_l_260_, 1);
v_v_275_ = lean_ctor_get(v_l_260_, 2);
v_l_276_ = lean_ctor_get(v_l_260_, 3);
v_r_277_ = lean_ctor_get(v_l_260_, 4);
v_size_278_ = lean_ctor_get(v_r_261_, 0);
v___x_279_ = lean_unsigned_to_nat(2u);
v___x_280_ = lean_nat_mul(v___x_279_, v_size_278_);
v___x_281_ = lean_nat_dec_lt(v_size_273_, v___x_280_);
lean_dec(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_309_; 
lean_inc(v_r_277_);
lean_inc(v_l_276_);
lean_inc(v_v_275_);
lean_inc(v_k_274_);
v_isSharedCheck_309_ = !lean_is_exclusive(v_l_260_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; 
v_unused_310_ = lean_ctor_get(v_l_260_, 4);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_l_260_, 3);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_l_260_, 2);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_l_260_, 1);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_l_260_, 0);
lean_dec(v_unused_314_);
v___x_283_ = v_l_260_;
v_isShared_284_ = v_isSharedCheck_309_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_l_260_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_309_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_299_; 
v___x_285_ = lean_nat_add(v___x_255_, v_size_256_);
v___x_286_ = lean_nat_add(v___x_285_, v_size_257_);
lean_dec(v_size_257_);
if (lean_obj_tag(v_l_276_) == 0)
{
lean_object* v_size_307_; 
v_size_307_ = lean_ctor_get(v_l_276_, 0);
lean_inc(v_size_307_);
v___y_299_ = v_size_307_;
goto v___jp_298_;
}
else
{
lean_object* v___x_308_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___y_299_ = v___x_308_;
goto v___jp_298_;
}
v___jp_287_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_nat_add(v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec(v___y_289_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 4, v_r_261_);
lean_ctor_set(v___x_283_, 3, v_r_277_);
lean_ctor_set(v___x_283_, 2, v_v_259_);
lean_ctor_set(v___x_283_, 1, v_k_258_);
lean_ctor_set(v___x_283_, 0, v___x_291_);
v___x_293_ = v___x_283_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_k_258_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_v_259_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_r_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_r_261_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 4, v___x_293_);
lean_ctor_set(v___x_271_, 3, v___y_288_);
lean_ctor_set(v___x_271_, 2, v_v_275_);
lean_ctor_set(v___x_271_, 1, v_k_274_);
lean_ctor_set(v___x_271_, 0, v___x_286_);
v___x_295_ = v___x_271_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_k_274_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_v_275_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v___y_288_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = lean_nat_add(v___x_285_, v___y_299_);
lean_dec(v___y_299_);
lean_dec(v___x_285_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_l_276_);
lean_ctor_set(v___x_111_, 0, v___x_300_);
v___x_302_ = v___x_111_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_l_276_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = lean_nat_add(v___x_255_, v_size_278_);
if (lean_obj_tag(v_r_277_) == 0)
{
lean_object* v_size_304_; 
v_size_304_ = lean_ctor_get(v_r_277_, 0);
lean_inc(v_size_304_);
v___y_288_ = v___x_302_;
v___y_289_ = v___x_303_;
v___y_290_ = v_size_304_;
goto v___jp_287_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___y_288_ = v___x_302_;
v___y_289_ = v___x_303_;
v___y_290_ = v___x_305_;
goto v___jp_287_;
}
}
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
lean_del_object(v___x_111_);
v___x_315_ = lean_nat_add(v___x_255_, v_size_256_);
v___x_316_ = lean_nat_add(v___x_315_, v_size_257_);
lean_dec(v_size_257_);
v___x_317_ = lean_nat_add(v___x_315_, v_size_273_);
lean_dec(v___x_315_);
lean_inc_ref(v_l_108_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 4, v_l_260_);
lean_ctor_set(v___x_271_, 3, v_l_108_);
lean_ctor_set(v___x_271_, 2, v_v_107_);
lean_ctor_set(v___x_271_, 1, v_k_106_);
lean_ctor_set(v___x_271_, 0, v___x_317_);
v___x_319_ = v___x_271_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_l_108_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_l_260_);
v___x_319_ = v_reuseFailAlloc_332_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_isSharedCheck_326_ = !lean_is_exclusive(v_l_108_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_327_ = lean_ctor_get(v_l_108_, 4);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_l_108_, 3);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_l_108_, 2);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_108_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_108_, 0);
lean_dec(v_unused_331_);
v___x_321_ = v_l_108_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_dec(v_l_108_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 4, v_r_261_);
lean_ctor_set(v___x_321_, 3, v___x_319_);
lean_ctor_set(v___x_321_, 2, v_v_259_);
lean_ctor_set(v___x_321_, 1, v_k_258_);
lean_ctor_set(v___x_321_, 0, v___x_316_);
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_258_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_259_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_r_261_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_339_; 
v_l_339_ = lean_ctor_get(v_impl_254_, 3);
lean_inc(v_l_339_);
if (lean_obj_tag(v_l_339_) == 0)
{
lean_object* v_r_340_; lean_object* v_k_341_; lean_object* v_v_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_365_; 
v_r_340_ = lean_ctor_get(v_impl_254_, 4);
v_k_341_ = lean_ctor_get(v_impl_254_, 1);
v_v_342_ = lean_ctor_get(v_impl_254_, 2);
v_isSharedCheck_365_ = !lean_is_exclusive(v_impl_254_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; lean_object* v_unused_367_; 
v_unused_366_ = lean_ctor_get(v_impl_254_, 3);
lean_dec(v_unused_366_);
v_unused_367_ = lean_ctor_get(v_impl_254_, 0);
lean_dec(v_unused_367_);
v___x_344_ = v_impl_254_;
v_isShared_345_ = v_isSharedCheck_365_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_r_340_);
lean_inc(v_v_342_);
lean_inc(v_k_341_);
lean_dec(v_impl_254_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_365_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_k_346_; lean_object* v_v_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_361_; 
v_k_346_ = lean_ctor_get(v_l_339_, 1);
v_v_347_ = lean_ctor_get(v_l_339_, 2);
v_isSharedCheck_361_ = !lean_is_exclusive(v_l_339_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_362_ = lean_ctor_get(v_l_339_, 4);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_l_339_, 3);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_l_339_, 0);
lean_dec(v_unused_364_);
v___x_349_ = v_l_339_;
v_isShared_350_ = v_isSharedCheck_361_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_v_347_);
lean_inc(v_k_346_);
lean_dec(v_l_339_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_361_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_340_, 2);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 4, v_r_340_);
lean_ctor_set(v___x_349_, 3, v_r_340_);
lean_ctor_set(v___x_349_, 2, v_v_107_);
lean_ctor_set(v___x_349_, 1, v_k_106_);
lean_ctor_set(v___x_349_, 0, v___x_255_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_r_340_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_r_340_);
v___x_353_ = v_reuseFailAlloc_360_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
lean_inc(v_r_340_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 3, v_r_340_);
lean_ctor_set(v___x_344_, 0, v___x_255_);
v___x_355_ = v___x_344_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_k_341_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_v_342_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_r_340_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v_r_340_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v___x_355_);
lean_ctor_set(v___x_111_, 3, v___x_353_);
lean_ctor_set(v___x_111_, 2, v_v_347_);
lean_ctor_set(v___x_111_, 1, v_k_346_);
lean_ctor_set(v___x_111_, 0, v___x_351_);
v___x_357_ = v___x_111_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_k_346_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_v_347_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
else
{
lean_object* v_r_368_; 
v_r_368_ = lean_ctor_get(v_impl_254_, 4);
lean_inc(v_r_368_);
if (lean_obj_tag(v_r_368_) == 0)
{
lean_object* v_k_369_; lean_object* v_v_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_381_; 
v_k_369_ = lean_ctor_get(v_impl_254_, 1);
v_v_370_ = lean_ctor_get(v_impl_254_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_impl_254_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; lean_object* v_unused_383_; lean_object* v_unused_384_; 
v_unused_382_ = lean_ctor_get(v_impl_254_, 4);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_impl_254_, 3);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_impl_254_, 0);
lean_dec(v_unused_384_);
v___x_372_ = v_impl_254_;
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_v_370_);
lean_inc(v_k_369_);
lean_dec(v_impl_254_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(3u);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_l_339_);
lean_ctor_set(v___x_372_, 2, v_v_107_);
lean_ctor_set(v___x_372_, 1, v_k_106_);
lean_ctor_set(v___x_372_, 0, v___x_255_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_l_339_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_l_339_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_r_368_);
lean_ctor_set(v___x_111_, 3, v___x_376_);
lean_ctor_set(v___x_111_, 2, v_v_370_);
lean_ctor_set(v___x_111_, 1, v_k_369_);
lean_ctor_set(v___x_111_, 0, v___x_374_);
v___x_378_ = v___x_111_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_k_369_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_v_370_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_r_368_);
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
else
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_unsigned_to_nat(2u);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 4, v_impl_254_);
lean_ctor_set(v___x_111_, 3, v_r_368_);
lean_ctor_set(v___x_111_, 0, v___x_385_);
v___x_387_ = v___x_111_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_v_107_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_r_368_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_impl_254_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
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
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_k_102_);
lean_ctor_set(v___x_391_, 2, v_v_103_);
lean_ctor_set(v___x_391_, 3, v_t_104_);
lean_ctor_set(v___x_391_, 4, v_t_104_);
return v___x_391_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object* v_k_392_, lean_object* v_t_393_){
_start:
{
if (lean_obj_tag(v_t_393_) == 0)
{
lean_object* v_k_394_; lean_object* v_l_395_; lean_object* v_r_396_; uint8_t v___x_397_; 
v_k_394_ = lean_ctor_get(v_t_393_, 1);
v_l_395_ = lean_ctor_get(v_t_393_, 3);
v_r_396_ = lean_ctor_get(v_t_393_, 4);
v___x_397_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_392_, v_k_394_);
switch(v___x_397_)
{
case 0:
{
v_t_393_ = v_l_395_;
goto _start;
}
case 1:
{
uint8_t v___x_399_; 
v___x_399_ = 1;
return v___x_399_;
}
default: 
{
v_t_393_ = v_r_396_;
goto _start;
}
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object* v_k_402_, lean_object* v_t_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_402_, v_t_403_);
lean_dec(v_t_403_);
lean_dec(v_k_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* v_x_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
switch(lean_obj_tag(v_x_406_))
{
case 6:
{
lean_object* v_b_409_; lean_object* v_c_410_; lean_object* v_set_411_; lean_object* v_order_412_; uint8_t v___x_413_; 
v_b_409_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_b_409_);
v_c_410_ = lean_ctor_get(v_x_406_, 3);
lean_inc(v_c_410_);
lean_dec_ref_known(v_x_406_, 5);
v_set_411_ = lean_ctor_get(v_a_408_, 0);
v_order_412_ = lean_ctor_get(v_a_408_, 1);
v___x_413_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_c_410_, v_set_411_);
if (v___x_413_ == 0)
{
lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_424_; 
lean_inc_ref(v_order_412_);
lean_inc(v_set_411_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_a_408_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_a_408_, 0);
lean_dec(v_unused_426_);
v___x_415_ = v_a_408_;
v_isShared_416_ = v_isSharedCheck_424_;
goto v_resetjp_414_;
}
else
{
lean_dec(v_a_408_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_424_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_417_ = lean_box(0);
lean_inc(v_c_410_);
v___x_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_c_410_, v___x_417_, v_set_411_);
v___x_419_ = lean_array_push(v_order_412_, v_c_410_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_419_);
lean_ctor_set(v___x_415_, 0, v___x_418_);
v___x_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_423_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
v_x_406_ = v_b_409_;
v_a_408_ = v___x_421_;
goto _start;
}
}
}
else
{
lean_dec(v_c_410_);
v_x_406_ = v_b_409_;
goto _start;
}
}
case 7:
{
lean_object* v_b_428_; lean_object* v_c_429_; lean_object* v_set_430_; lean_object* v_order_431_; uint8_t v___x_432_; 
v_b_428_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_b_428_);
v_c_429_ = lean_ctor_get(v_x_406_, 2);
lean_inc(v_c_429_);
lean_dec_ref_known(v_x_406_, 4);
v_set_430_ = lean_ctor_get(v_a_408_, 0);
v_order_431_ = lean_ctor_get(v_a_408_, 1);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_c_429_, v_set_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
lean_inc_ref(v_order_431_);
lean_inc(v_set_430_);
v_isSharedCheck_443_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_444_ = lean_ctor_get(v_a_408_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_a_408_, 0);
lean_dec(v_unused_445_);
v___x_434_ = v_a_408_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_a_408_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_436_ = lean_box(0);
lean_inc(v_c_429_);
v___x_437_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_c_429_, v___x_436_, v_set_430_);
v___x_438_ = lean_array_push(v_order_431_, v_c_429_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_438_);
lean_ctor_set(v___x_434_, 0, v___x_437_);
v___x_440_ = v___x_434_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_442_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v_x_406_ = v_b_428_;
v_a_408_ = v___x_440_;
goto _start;
}
}
}
else
{
lean_dec(v_c_429_);
v_x_406_ = v_b_428_;
goto _start;
}
}
case 19:
{
lean_object* v_v_447_; lean_object* v_b_448_; lean_object* v___x_449_; lean_object* v_snd_450_; 
v_v_447_ = lean_ctor_get(v_x_406_, 2);
lean_inc(v_v_447_);
v_b_448_ = lean_ctor_get(v_x_406_, 3);
lean_inc(v_b_448_);
lean_dec_ref_known(v_x_406_, 4);
v___x_449_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_447_, v_a_407_, v_a_408_);
v_snd_450_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_snd_450_);
lean_dec_ref(v___x_449_);
v_x_406_ = v_b_448_;
v_a_408_ = v_snd_450_;
goto _start;
}
case 27:
{
lean_object* v_cs_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_cs_452_ = lean_ctor_get(v_x_406_, 3);
lean_inc_ref(v_cs_452_);
lean_dec_ref_known(v_x_406_, 4);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_array_get_size(v_cs_452_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_nat_dec_lt(v___x_453_, v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_dec_ref(v_cs_452_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v_a_408_);
return v___x_457_;
}
else
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((size_t)0ULL);
v___x_459_ = lean_usize_of_nat(v___x_454_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_452_, v___x_458_, v___x_459_, v___x_455_, v_a_407_, v_a_408_);
lean_dec_ref(v_cs_452_);
return v___x_460_;
}
}
default: 
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_IR_FnBody_isTerminal(v_x_406_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_IR_FnBody_body(v_x_406_);
lean_dec(v_x_406_);
v_x_406_ = v___x_462_;
goto _start;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v_x_406_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_a_408_);
return v___x_465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object* v_as_466_, size_t v_i_467_, size_t v_stop_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_eq(v_i_467_, v_stop_468_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; lean_object* v_snd_477_; size_t v___x_478_; size_t v___x_479_; 
v___x_473_ = lean_array_uget_borrowed(v_as_466_, v_i_467_);
v___x_474_ = l_Lean_IR_Alt_body(v___x_473_);
v___x_475_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v___x_474_, v___y_470_, v___y_471_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_fst_476_);
v_snd_477_ = lean_ctor_get(v___x_475_, 1);
lean_inc(v_snd_477_);
lean_dec_ref(v___x_475_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_i_467_, v___x_478_);
v_i_467_ = v___x_479_;
v_b_469_ = v_fst_476_;
v___y_471_ = v_snd_477_;
goto _start;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_b_469_);
lean_ctor_set(v___x_481_, 1, v___y_471_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object* v_as_482_, lean_object* v_i_483_, lean_object* v_stop_484_, lean_object* v_b_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
size_t v_i_boxed_488_; size_t v_stop_boxed_489_; lean_object* v_res_490_; 
v_i_boxed_488_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_stop_boxed_489_ = lean_unbox_usize(v_stop_484_);
lean_dec(v_stop_484_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_482_, v_i_boxed_488_, v_stop_boxed_489_, v_b_485_, v___y_486_, v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_as_482_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* v_x_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_491_, v_a_492_, v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object* v_00_u03b2_495_, lean_object* v_k_496_, lean_object* v_t_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_496_, v_t_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_499_, lean_object* v_k_500_, lean_object* v_t_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_499_, v_k_500_, v_t_501_);
lean_dec(v_t_501_);
lean_dec(v_k_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object* v_00_u03b2_504_, lean_object* v_k_505_, lean_object* v_v_506_, lean_object* v_t_507_, lean_object* v_hl_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_505_, v_v_506_, v_t_507_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* v_fn_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_513_; 
lean_inc_ref(v_a_511_);
v___x_513_ = lean_get_init_fn_name_for(v_a_511_, v_fn_510_);
if (lean_obj_tag(v___x_513_) == 1)
{
lean_object* v_val_514_; lean_object* v_set_515_; lean_object* v_order_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v___x_513_, 1);
v_set_515_ = lean_ctor_get(v_a_512_, 0);
v_order_516_ = lean_ctor_get(v_a_512_, 1);
v___x_517_ = lean_box(0);
v___x_518_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_514_, v_set_515_);
if (v___x_518_ == 0)
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
lean_inc_ref(v_order_516_);
lean_inc(v_set_515_);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_512_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_529_ = lean_ctor_get(v_a_512_, 1);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_a_512_, 0);
lean_dec(v_unused_530_);
v___x_520_ = v_a_512_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_a_512_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
lean_inc(v_val_514_);
v___x_522_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_514_, v___x_517_, v_set_515_);
v___x_523_ = lean_array_push(v_order_516_, v_val_514_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 1, v___x_523_);
lean_ctor_set(v___x_520_, 0, v___x_522_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_523_);
v___x_525_ = v_reuseFailAlloc_527_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_517_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
return v___x_526_;
}
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v_val_514_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_517_);
lean_ctor_set(v___x_531_, 1, v_a_512_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v___x_513_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_a_512_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object* v_fn_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_534_, v_a_535_, v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_f_541_; lean_object* v_body_542_; lean_object* v___x_543_; lean_object* v_snd_544_; lean_object* v___x_545_; 
v_f_541_ = lean_ctor_get(v_x_538_, 0);
lean_inc(v_f_541_);
v_body_542_ = lean_ctor_get(v_x_538_, 3);
lean_inc(v_body_542_);
lean_dec_ref_known(v_x_538_, 5);
v___x_543_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_541_, v_a_539_, v_a_540_);
v_snd_544_ = lean_ctor_get(v___x_543_, 1);
lean_inc(v_snd_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_542_, v_a_539_, v_snd_544_);
return v___x_545_;
}
else
{
lean_object* v_f_546_; lean_object* v___x_547_; 
v_f_546_ = lean_ctor_get(v_x_538_, 0);
lean_inc(v_f_546_);
lean_dec_ref_known(v_x_538_, 4);
v___x_547_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_546_, v_a_539_, v_a_540_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object* v_x_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_548_, v_a_549_, v_a_550_);
lean_dec_ref(v_a_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
if (lean_obj_tag(v_as_552_) == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___y_554_);
return v___x_556_;
}
else
{
lean_object* v_head_557_; lean_object* v_tail_558_; lean_object* v___x_559_; lean_object* v_snd_560_; lean_object* v_set_561_; lean_object* v_order_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_head_557_ = lean_ctor_get(v_as_552_, 0);
lean_inc_n(v_head_557_, 2);
v_tail_558_ = lean_ctor_get(v_as_552_, 1);
lean_inc(v_tail_558_);
lean_dec_ref_known(v_as_552_, 2);
v___x_559_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_557_, v___y_553_, v___y_554_);
v_snd_560_ = lean_ctor_get(v___x_559_, 1);
lean_inc(v_snd_560_);
lean_dec_ref(v___x_559_);
v_set_561_ = lean_ctor_get(v_snd_560_, 0);
v_order_562_ = lean_ctor_get(v_snd_560_, 1);
v___x_563_ = l_Lean_IR_Decl_name(v_head_557_);
lean_dec(v_head_557_);
v___x_564_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_563_, v_set_561_);
if (v___x_564_ == 0)
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_575_; 
lean_inc_ref(v_order_562_);
lean_inc(v_set_561_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; 
v_unused_576_ = lean_ctor_get(v_snd_560_, 1);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_snd_560_, 0);
lean_dec(v_unused_577_);
v___x_566_ = v_snd_560_;
v_isShared_567_ = v_isSharedCheck_575_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_snd_560_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_575_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_568_ = lean_box(0);
lean_inc(v___x_563_);
v___x_569_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_563_, v___x_568_, v_set_561_);
v___x_570_ = lean_array_push(v_order_562_, v___x_563_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_570_);
lean_ctor_set(v___x_566_, 0, v___x_569_);
v___x_572_ = v___x_566_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v_as_552_ = v_tail_558_;
v___y_554_ = v___x_572_;
goto _start;
}
}
}
else
{
lean_dec(v___x_563_);
v_as_552_ = v_tail_558_;
v___y_554_ = v_snd_560_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object* v_as_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_as_579_, v___y_580_, v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_583_, v_a_584_, v_a_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object* v_decls_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_587_, v_a_588_, v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_590_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_594_ = l_Lean_NameSet_empty;
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_596_, lean_object* v_decls_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_snd_600_; lean_object* v_order_601_; 
v___x_598_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_599_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_597_, v_env_596_, v___x_598_);
v_snd_600_ = lean_ctor_get(v___x_599_, 1);
lean_inc(v_snd_600_);
lean_dec_ref(v___x_599_);
v_order_601_ = lean_ctor_get(v_snd_600_, 1);
lean_inc_ref(v_order_601_);
lean_dec(v_snd_600_);
return v_order_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object* v_env_602_, lean_object* v_decls_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_IR_collectUsedDecls(v_env_602_, v_decls_603_);
lean_dec_ref(v_env_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_607_, lean_object* v_t_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_621_; 
v_fst_610_ = lean_ctor_get(v_x_609_, 0);
v_snd_611_ = lean_ctor_get(v_x_609_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_609_);
if (v_isSharedCheck_621_ == 0)
{
v___x_613_ = v_x_609_;
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snd_611_);
lean_inc(v_fst_610_);
lean_dec(v_x_609_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_621_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_615_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_616_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_615_, v___x_616_, v_fst_610_, v_x_607_, v_t_608_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_617_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_snd_611_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
return v_x_622_;
}
else
{
lean_object* v_key_624_; lean_object* v_value_625_; lean_object* v_tail_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_649_; 
v_key_624_ = lean_ctor_get(v_x_623_, 0);
v_value_625_ = lean_ctor_get(v_x_623_, 1);
v_tail_626_ = lean_ctor_get(v_x_623_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_649_ == 0)
{
v___x_628_ = v_x_623_;
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_tail_626_);
lean_inc(v_value_625_);
lean_inc(v_key_624_);
lean_dec(v_x_623_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_649_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v_fold_634_; uint64_t v___x_635_; uint64_t v___x_636_; uint64_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_630_ = lean_array_get_size(v_x_622_);
v___x_631_ = l_Lean_IR_instHashableVarId_hash(v_key_624_);
v___x_632_ = 32ULL;
v___x_633_ = lean_uint64_shift_right(v___x_631_, v___x_632_);
v_fold_634_ = lean_uint64_xor(v___x_631_, v___x_633_);
v___x_635_ = 16ULL;
v___x_636_ = lean_uint64_shift_right(v_fold_634_, v___x_635_);
v___x_637_ = lean_uint64_xor(v_fold_634_, v___x_636_);
v___x_638_ = lean_uint64_to_usize(v___x_637_);
v___x_639_ = lean_usize_of_nat(v___x_630_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_sub(v___x_639_, v___x_640_);
v___x_642_ = lean_usize_land(v___x_638_, v___x_641_);
v___x_643_ = lean_array_uget_borrowed(v_x_622_, v___x_642_);
lean_inc(v___x_643_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 2, v___x_643_);
v___x_645_ = v___x_628_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_key_624_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_value_625_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v___x_643_);
v___x_645_ = v_reuseFailAlloc_648_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_uset(v_x_622_, v___x_642_, v___x_645_);
v_x_622_ = v___x_646_;
v_x_623_ = v_tail_626_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_650_, lean_object* v_source_651_, lean_object* v_target_652_){
_start:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_array_get_size(v_source_651_);
v___x_654_ = lean_nat_dec_lt(v_i_650_, v___x_653_);
if (v___x_654_ == 0)
{
lean_dec_ref(v_source_651_);
lean_dec(v_i_650_);
return v_target_652_;
}
else
{
lean_object* v_es_655_; lean_object* v___x_656_; lean_object* v_source_657_; lean_object* v_target_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_es_655_ = lean_array_fget(v_source_651_, v_i_650_);
v___x_656_ = lean_box(0);
v_source_657_ = lean_array_fset(v_source_651_, v_i_650_, v___x_656_);
v_target_658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_652_, v_es_655_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_add(v_i_650_, v___x_659_);
lean_dec(v_i_650_);
v_i_650_ = v___x_660_;
v_source_651_ = v_source_657_;
v_target_652_ = v_target_658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_nbuckets_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_663_ = lean_array_get_size(v_data_662_);
v___x_664_ = lean_unsigned_to_nat(2u);
v_nbuckets_665_ = lean_nat_mul(v___x_663_, v___x_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_box(0);
v___x_668_ = lean_mk_array(v_nbuckets_665_, v___x_667_);
v___x_669_ = lean_array_propagate_mark(v_data_662_, v___x_668_);
v___x_670_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_666_, v_data_662_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_672_) == 0)
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
else
{
lean_object* v_key_674_; lean_object* v_tail_675_; uint8_t v___x_676_; 
v_key_674_ = lean_ctor_get(v_x_672_, 0);
v_tail_675_ = lean_ctor_get(v_x_672_, 2);
v___x_676_ = l_Lean_IR_instBEqVarId_beq(v_key_674_, v_a_671_);
if (v___x_676_ == 0)
{
v_x_672_ = v_tail_675_;
goto _start;
}
else
{
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_678_, v_x_679_);
lean_dec(v_x_679_);
lean_dec(v_a_678_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_682_, lean_object* v_b_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_dec(v_b_683_);
lean_dec(v_a_682_);
return v_x_684_;
}
else
{
lean_object* v_key_685_; lean_object* v_value_686_; lean_object* v_tail_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_699_; 
v_key_685_ = lean_ctor_get(v_x_684_, 0);
v_value_686_ = lean_ctor_get(v_x_684_, 1);
v_tail_687_ = lean_ctor_get(v_x_684_, 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_699_ == 0)
{
v___x_689_ = v_x_684_;
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_tail_687_);
lean_inc(v_value_686_);
lean_inc(v_key_685_);
lean_dec(v_x_684_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_IR_instBEqVarId_beq(v_key_685_, v_a_682_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_682_, v_b_683_, v_tail_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 2, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_key_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_value_686_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v___x_697_; 
lean_dec(v_value_686_);
lean_dec(v_key_685_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v_b_683_);
lean_ctor_set(v___x_689_, 0, v_a_682_);
v___x_697_ = v___x_689_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_b_683_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_tail_687_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_700_, lean_object* v_a_701_, lean_object* v_b_702_){
_start:
{
lean_object* v_size_703_; lean_object* v_buckets_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_747_; 
v_size_703_ = lean_ctor_get(v_m_700_, 0);
v_buckets_704_ = lean_ctor_get(v_m_700_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_m_700_);
if (v_isSharedCheck_747_ == 0)
{
v___x_706_ = v_m_700_;
v_isShared_707_ = v_isSharedCheck_747_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_buckets_704_);
lean_inc(v_size_703_);
lean_dec(v_m_700_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_747_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v_bkt_721_; uint8_t v___x_722_; 
v___x_708_ = lean_array_get_size(v_buckets_704_);
v___x_709_ = l_Lean_IR_instHashableVarId_hash(v_a_701_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_708_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v_bkt_721_ = lean_array_uget_borrowed(v_buckets_704_, v___x_720_);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_701_, v_bkt_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v_size_x27_724_; lean_object* v___x_725_; lean_object* v_buckets_x27_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_723_ = lean_unsigned_to_nat(1u);
v_size_x27_724_ = lean_nat_add(v_size_703_, v___x_723_);
lean_dec(v_size_703_);
lean_inc(v_bkt_721_);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v_a_701_);
lean_ctor_set(v___x_725_, 1, v_b_702_);
lean_ctor_set(v___x_725_, 2, v_bkt_721_);
v_buckets_x27_726_ = lean_array_uset(v_buckets_704_, v___x_720_, v___x_725_);
v___x_727_ = lean_unsigned_to_nat(4u);
v___x_728_ = lean_nat_mul(v_size_x27_724_, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(3u);
v___x_730_ = lean_nat_div(v___x_728_, v___x_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_array_get_size(v_buckets_x27_726_);
v___x_732_ = lean_nat_dec_le(v___x_730_, v___x_731_);
lean_dec(v___x_730_);
if (v___x_732_ == 0)
{
lean_object* v_val_733_; lean_object* v___x_735_; 
v_val_733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_726_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v_val_733_);
lean_ctor_set(v___x_706_, 0, v_size_x27_724_);
v___x_735_ = v___x_706_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_size_x27_724_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_val_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
else
{
lean_object* v___x_738_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v_buckets_x27_726_);
lean_ctor_set(v___x_706_, 0, v_size_x27_724_);
v___x_738_ = v___x_706_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_x27_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_buckets_x27_726_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v___x_740_; lean_object* v_buckets_x27_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
lean_inc(v_bkt_721_);
v___x_740_ = lean_box(0);
v_buckets_x27_741_ = lean_array_uset(v_buckets_704_, v___x_720_, v___x_740_);
v___x_742_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_701_, v_b_702_, v_bkt_721_);
v___x_743_ = lean_array_uset(v_buckets_x27_741_, v___x_720_, v___x_742_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_743_);
v___x_745_ = v___x_706_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_size_703_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_748_, size_t v_i_749_, size_t v_stop_750_, lean_object* v_b_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_eq(v_i_749_, v_stop_750_);
if (v___x_752_ == 0)
{
lean_object* v_fst_753_; lean_object* v_snd_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_768_; 
v_fst_753_ = lean_ctor_get(v_b_751_, 0);
v_snd_754_ = lean_ctor_get(v_b_751_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_b_751_);
if (v_isSharedCheck_768_ == 0)
{
v___x_756_ = v_b_751_;
v_isShared_757_ = v_isSharedCheck_768_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_snd_754_);
lean_inc(v_fst_753_);
lean_dec(v_b_751_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_768_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v_x_759_; lean_object* v_ty_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_758_ = lean_array_uget_borrowed(v_as_748_, v_i_749_);
v_x_759_ = lean_ctor_get(v___x_758_, 0);
v_ty_760_ = lean_ctor_get(v___x_758_, 1);
lean_inc(v_ty_760_);
lean_inc(v_x_759_);
v___x_761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_753_, v_x_759_, v_ty_760_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_761_);
v___x_763_ = v___x_756_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_snd_754_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
size_t v___x_764_; size_t v___x_765_; 
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_749_, v___x_764_);
v_i_749_ = v___x_765_;
v_b_751_ = v___x_763_;
goto _start;
}
}
}
else
{
return v_b_751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_769_, lean_object* v_i_770_, lean_object* v_stop_771_, lean_object* v_b_772_){
_start:
{
size_t v_i_boxed_773_; size_t v_stop_boxed_774_; lean_object* v_res_775_; 
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_stop_boxed_774_ = lean_unbox_usize(v_stop_771_);
lean_dec(v_stop_771_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_769_, v_i_boxed_773_, v_stop_boxed_774_, v_b_772_);
lean_dec_ref(v_as_769_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_776_, lean_object* v_s_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_array_get_size(v_ps_776_);
v___x_780_ = lean_nat_dec_lt(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
return v_s_777_;
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_779_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_776_, v___x_781_, v___x_782_, v_s_777_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_784_, lean_object* v_s_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_IR_CollectMaps_collectParams(v_ps_784_, v_s_785_);
lean_dec_ref(v_ps_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_787_, lean_object* v_m_788_, lean_object* v_a_789_, lean_object* v_b_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_788_, v_a_789_, v_b_790_);
return v___x_791_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_792_, lean_object* v_a_793_, lean_object* v_x_794_){
_start:
{
uint8_t v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_796_, lean_object* v_a_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_796_, v_a_797_, v_x_798_);
lean_dec(v_x_798_);
lean_dec(v_a_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_801_, lean_object* v_data_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_804_, lean_object* v_a_805_, lean_object* v_b_806_, lean_object* v_x_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_805_, v_b_806_, v_x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_809_, lean_object* v_i_810_, lean_object* v_source_811_, lean_object* v_target_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_810_, v_source_811_, v_target_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_815_, v_x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_820_, lean_object* v_xs_821_, lean_object* v_x_822_){
_start:
{
lean_object* v_fst_823_; lean_object* v_snd_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_fst_823_ = lean_ctor_get(v_x_822_, 0);
v_snd_824_ = lean_ctor_get(v_x_822_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_822_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v_x_822_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_snd_824_);
lean_inc(v_fst_823_);
lean_dec(v_x_822_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_828_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_829_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_828_, v___x_829_, v_snd_824_, v_j_820_, v_xs_821_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_fst_823_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
uint8_t v___x_837_; 
v___x_837_ = 0;
return v___x_837_;
}
else
{
lean_object* v_key_838_; lean_object* v_tail_839_; uint8_t v___x_840_; 
v_key_838_ = lean_ctor_get(v_x_836_, 0);
v_tail_839_ = lean_ctor_get(v_x_836_, 2);
v___x_840_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_838_, v_a_835_);
if (v___x_840_ == 0)
{
v_x_836_ = v_tail_839_;
goto _start;
}
else
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_842_, v_x_843_);
lean_dec(v_x_843_);
lean_dec(v_a_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
return v_x_846_;
}
else
{
lean_object* v_key_848_; lean_object* v_value_849_; lean_object* v_tail_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_873_; 
v_key_848_ = lean_ctor_get(v_x_847_, 0);
v_value_849_ = lean_ctor_get(v_x_847_, 1);
v_tail_850_ = lean_ctor_get(v_x_847_, 2);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_873_ == 0)
{
v___x_852_ = v_x_847_;
v_isShared_853_ = v_isSharedCheck_873_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_tail_850_);
lean_inc(v_value_849_);
lean_inc(v_key_848_);
lean_dec(v_x_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_873_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v_fold_858_; uint64_t v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_854_ = lean_array_get_size(v_x_846_);
v___x_855_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_848_);
v___x_856_ = 32ULL;
v___x_857_ = lean_uint64_shift_right(v___x_855_, v___x_856_);
v_fold_858_ = lean_uint64_xor(v___x_855_, v___x_857_);
v___x_859_ = 16ULL;
v___x_860_ = lean_uint64_shift_right(v_fold_858_, v___x_859_);
v___x_861_ = lean_uint64_xor(v_fold_858_, v___x_860_);
v___x_862_ = lean_uint64_to_usize(v___x_861_);
v___x_863_ = lean_usize_of_nat(v___x_854_);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_sub(v___x_863_, v___x_864_);
v___x_866_ = lean_usize_land(v___x_862_, v___x_865_);
v___x_867_ = lean_array_uget_borrowed(v_x_846_, v___x_866_);
lean_inc(v___x_867_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 2, v___x_867_);
v___x_869_ = v___x_852_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_key_848_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_value_849_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v___x_867_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
v___x_870_ = lean_array_uset(v_x_846_, v___x_866_, v___x_869_);
v_x_846_ = v___x_870_;
v_x_847_ = v_tail_850_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_874_, lean_object* v_source_875_, lean_object* v_target_876_){
_start:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_array_get_size(v_source_875_);
v___x_878_ = lean_nat_dec_lt(v_i_874_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec_ref(v_source_875_);
lean_dec(v_i_874_);
return v_target_876_;
}
else
{
lean_object* v_es_879_; lean_object* v___x_880_; lean_object* v_source_881_; lean_object* v_target_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_es_879_ = lean_array_fget(v_source_875_, v_i_874_);
v___x_880_ = lean_box(0);
v_source_881_ = lean_array_fset(v_source_875_, v_i_874_, v___x_880_);
v_target_882_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_876_, v_es_879_);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_add(v_i_874_, v___x_883_);
lean_dec(v_i_874_);
v_i_874_ = v___x_884_;
v_source_875_ = v_source_881_;
v_target_876_ = v_target_882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_nbuckets_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_887_ = lean_array_get_size(v_data_886_);
v___x_888_ = lean_unsigned_to_nat(2u);
v_nbuckets_889_ = lean_nat_mul(v___x_887_, v___x_888_);
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = lean_box(0);
v___x_892_ = lean_mk_array(v_nbuckets_889_, v___x_891_);
v___x_893_ = lean_array_propagate_mark(v_data_886_, v___x_892_);
v___x_894_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_890_, v_data_886_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_895_, lean_object* v_b_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_dec(v_b_896_);
lean_dec(v_a_895_);
return v_x_897_;
}
else
{
lean_object* v_key_898_; lean_object* v_value_899_; lean_object* v_tail_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_912_; 
v_key_898_ = lean_ctor_get(v_x_897_, 0);
v_value_899_ = lean_ctor_get(v_x_897_, 1);
v_tail_900_ = lean_ctor_get(v_x_897_, 2);
v_isSharedCheck_912_ = !lean_is_exclusive(v_x_897_);
if (v_isSharedCheck_912_ == 0)
{
v___x_902_ = v_x_897_;
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_tail_900_);
lean_inc(v_value_899_);
lean_inc(v_key_898_);
lean_dec(v_x_897_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_898_, v_a_895_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_895_, v_b_896_, v_tail_900_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 2, v___x_905_);
v___x_907_ = v___x_902_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_key_898_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_value_899_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
else
{
lean_object* v___x_910_; 
lean_dec(v_value_899_);
lean_dec(v_key_898_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v_b_896_);
lean_ctor_set(v___x_902_, 0, v_a_895_);
v___x_910_ = v___x_902_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_895_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_b_896_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_tail_900_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_913_, lean_object* v_a_914_, lean_object* v_b_915_){
_start:
{
lean_object* v_size_916_; lean_object* v_buckets_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_960_; 
v_size_916_ = lean_ctor_get(v_m_913_, 0);
v_buckets_917_ = lean_ctor_get(v_m_913_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_m_913_);
if (v_isSharedCheck_960_ == 0)
{
v___x_919_ = v_m_913_;
v_isShared_920_ = v_isSharedCheck_960_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_buckets_917_);
lean_inc(v_size_916_);
lean_dec(v_m_913_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_960_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; uint64_t v___x_924_; uint64_t v_fold_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v___x_928_; size_t v___x_929_; size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; lean_object* v_bkt_934_; uint8_t v___x_935_; 
v___x_921_ = lean_array_get_size(v_buckets_917_);
v___x_922_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_914_);
v___x_923_ = 32ULL;
v___x_924_ = lean_uint64_shift_right(v___x_922_, v___x_923_);
v_fold_925_ = lean_uint64_xor(v___x_922_, v___x_924_);
v___x_926_ = 16ULL;
v___x_927_ = lean_uint64_shift_right(v_fold_925_, v___x_926_);
v___x_928_ = lean_uint64_xor(v_fold_925_, v___x_927_);
v___x_929_ = lean_uint64_to_usize(v___x_928_);
v___x_930_ = lean_usize_of_nat(v___x_921_);
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_sub(v___x_930_, v___x_931_);
v___x_933_ = lean_usize_land(v___x_929_, v___x_932_);
v_bkt_934_ = lean_array_uget_borrowed(v_buckets_917_, v___x_933_);
v___x_935_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_914_, v_bkt_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v_size_x27_937_; lean_object* v___x_938_; lean_object* v_buckets_x27_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v_size_x27_937_ = lean_nat_add(v_size_916_, v___x_936_);
lean_dec(v_size_916_);
lean_inc(v_bkt_934_);
v___x_938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_938_, 0, v_a_914_);
lean_ctor_set(v___x_938_, 1, v_b_915_);
lean_ctor_set(v___x_938_, 2, v_bkt_934_);
v_buckets_x27_939_ = lean_array_uset(v_buckets_917_, v___x_933_, v___x_938_);
v___x_940_ = lean_unsigned_to_nat(4u);
v___x_941_ = lean_nat_mul(v_size_x27_937_, v___x_940_);
v___x_942_ = lean_unsigned_to_nat(3u);
v___x_943_ = lean_nat_div(v___x_941_, v___x_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_array_get_size(v_buckets_x27_939_);
v___x_945_ = lean_nat_dec_le(v___x_943_, v___x_944_);
lean_dec(v___x_943_);
if (v___x_945_ == 0)
{
lean_object* v_val_946_; lean_object* v___x_948_; 
v_val_946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_939_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v_val_946_);
lean_ctor_set(v___x_919_, 0, v_size_x27_937_);
v___x_948_ = v___x_919_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_size_x27_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_val_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_object* v___x_951_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v_buckets_x27_939_);
lean_ctor_set(v___x_919_, 0, v_size_x27_937_);
v___x_951_ = v___x_919_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_size_x27_937_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_buckets_x27_939_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v___x_953_; lean_object* v_buckets_x27_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_958_; 
lean_inc(v_bkt_934_);
v___x_953_ = lean_box(0);
v_buckets_x27_954_ = lean_array_uset(v_buckets_917_, v___x_933_, v___x_953_);
v___x_955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_914_, v_b_915_, v_bkt_934_);
v___x_956_ = lean_array_uset(v_buckets_x27_954_, v___x_933_, v___x_955_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v___x_956_);
v___x_958_ = v___x_919_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_size_916_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_961_, lean_object* v_a_962_){
_start:
{
switch(lean_obj_tag(v_x_961_))
{
case 19:
{
lean_object* v_j_963_; lean_object* v_xs_964_; lean_object* v_v_965_; lean_object* v_b_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_j_963_ = lean_ctor_get(v_x_961_, 0);
lean_inc(v_j_963_);
v_xs_964_ = lean_ctor_get(v_x_961_, 1);
lean_inc_ref(v_xs_964_);
v_v_965_ = lean_ctor_get(v_x_961_, 2);
lean_inc(v_v_965_);
v_b_966_ = lean_ctor_get(v_x_961_, 3);
lean_inc(v_b_966_);
lean_dec_ref_known(v_x_961_, 4);
v___x_967_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_966_, v_a_962_);
v___x_968_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_965_, v___x_967_);
v___x_969_ = l_Lean_IR_CollectMaps_collectParams(v_xs_964_, v___x_968_);
v_fst_970_ = lean_ctor_get(v___x_969_, 0);
v_snd_971_ = lean_ctor_get(v___x_969_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_979_ == 0)
{
v___x_973_ = v___x_969_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_snd_971_);
lean_inc(v_fst_970_);
lean_dec(v___x_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_971_, v_j_963_, v_xs_964_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_fst_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
case 27:
{
lean_object* v_cs_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_cs_980_ = lean_ctor_get(v_x_961_, 3);
lean_inc_ref(v_cs_980_);
lean_dec_ref_known(v_x_961_, 4);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_array_get_size(v_cs_980_);
v___x_983_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec_ref(v_cs_980_);
return v_a_962_;
}
else
{
size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_982_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_980_, v___x_984_, v___x_985_, v_a_962_);
lean_dec_ref(v_cs_980_);
return v___x_986_;
}
}
default: 
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_IR_FnBody_isVarDecl(v_x_961_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_IR_FnBody_isTerminal(v_x_961_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_IR_FnBody_body(v_x_961_);
lean_dec(v_x_961_);
v_x_961_ = v___x_989_;
goto _start;
}
else
{
lean_dec(v_x_961_);
return v_a_962_;
}
}
else
{
lean_object* v_b_991_; lean_object* v___x_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1004_; 
v_b_991_ = l_Lean_IR_FnBody_body(v_x_961_);
v___x_992_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_991_, v_a_962_);
v_fst_993_ = lean_ctor_get(v___x_992_, 0);
v_snd_994_ = lean_ctor_get(v___x_992_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_996_ = v___x_992_;
v_isShared_997_ = v_isSharedCheck_1004_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_snd_994_);
lean_inc(v_fst_993_);
lean_dec(v___x_992_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1004_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_x_998_; lean_object* v_t_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_x_998_ = l_Lean_IR_FnBody_targetVar(v_x_961_);
v_t_999_ = l_Lean_IR_FnBody_targetType(v_x_961_);
lean_dec(v_x_961_);
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_993_, v_x_998_, v_t_999_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1000_);
v___x_1002_ = v___x_996_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_snd_994_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_1005_, size_t v_i_1006_, size_t v_stop_1007_, lean_object* v_b_1008_){
_start:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_eq(v_i_1006_, v_stop_1007_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; 
v___x_1010_ = lean_array_uget_borrowed(v_as_1005_, v_i_1006_);
v___x_1011_ = l_Lean_IR_Alt_body(v___x_1010_);
v___x_1012_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1011_, v_b_1008_);
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_add(v_i_1006_, v___x_1013_);
v_i_1006_ = v___x_1014_;
v_b_1008_ = v___x_1012_;
goto _start;
}
else
{
return v_b_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1016_, lean_object* v_i_1017_, lean_object* v_stop_1018_, lean_object* v_b_1019_){
_start:
{
size_t v_i_boxed_1020_; size_t v_stop_boxed_1021_; lean_object* v_res_1022_; 
v_i_boxed_1020_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_stop_boxed_1021_ = lean_unbox_usize(v_stop_1018_);
lean_dec(v_stop_1018_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1016_, v_i_boxed_1020_, v_stop_boxed_1021_, v_b_1019_);
lean_dec_ref(v_as_1016_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1024_, v_a_1025_, v_b_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1028_, lean_object* v_a_1029_, lean_object* v_x_1030_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1029_, v_x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1032_, lean_object* v_a_1033_, lean_object* v_x_1034_){
_start:
{
uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_res_1035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1032_, v_a_1033_, v_x_1034_);
lean_dec(v_x_1034_);
lean_dec(v_a_1033_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1037_, lean_object* v_data_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1041_, v_b_1042_, v_x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1045_, lean_object* v_i_1046_, lean_object* v_source_1047_, lean_object* v_target_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1046_, v_source_1047_, v_target_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1054_, lean_object* v_a_1055_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v_xs_1056_; lean_object* v_body_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_xs_1056_ = lean_ctor_get(v_x_1054_, 1);
lean_inc_ref(v_xs_1056_);
v_body_1057_ = lean_ctor_get(v_x_1054_, 3);
lean_inc(v_body_1057_);
lean_dec_ref_known(v_x_1054_, 5);
v___x_1058_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1057_, v_a_1055_);
v___x_1059_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1056_, v___x_1058_);
lean_dec_ref(v_xs_1056_);
return v___x_1059_;
}
else
{
lean_dec_ref(v_x_1054_);
return v_a_1055_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_unsigned_to_nat(16u);
v___x_1062_ = lean_mk_array(v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1070_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1068_, v___x_1069_);
return v___x_1070_;
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
