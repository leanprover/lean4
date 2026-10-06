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
lean_object* v_set_59_; lean_object* v_order_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_83_; 
v_set_59_ = lean_ctor_get(v_a_58_, 0);
v_order_60_ = lean_ctor_get(v_a_58_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_a_58_);
if (v_isSharedCheck_83_ == 0)
{
v___x_62_ = v_a_58_;
v_isShared_63_ = v_isSharedCheck_83_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_order_60_);
lean_inc(v_set_59_);
lean_dec(v_a_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_83_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v_fst_66_; lean_object* v_snd_67_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_64_ = lean_box(0);
v___x_78_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_59_);
lean_inc(v_f_57_);
v___x_79_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_78_, v_f_57_, v_set_59_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_inc(v_f_57_);
v___x_80_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_78_, v_f_57_, v___x_64_, v_set_59_);
v___x_81_ = lean_box(v___x_79_);
v_fst_66_ = v___x_81_;
v_snd_67_ = v___x_80_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(v___x_79_);
v_fst_66_ = v___x_82_;
v_snd_67_ = v_set_59_;
goto v___jp_65_;
}
v___jp_65_:
{
uint8_t v___x_68_; 
v___x_68_ = lean_unbox(v_fst_66_);
lean_dec(v_fst_66_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = lean_array_push(v_order_60_, v_f_57_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_69_);
lean_ctor_set(v___x_62_, 0, v_snd_67_);
v___x_71_ = v___x_62_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_snd_67_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___x_69_);
v___x_71_ = v_reuseFailAlloc_73_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; 
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_64_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
return v___x_72_;
}
}
else
{
lean_object* v___x_75_; 
lean_dec(v_f_57_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v_snd_67_);
v___x_75_ = v___x_62_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_snd_67_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_order_60_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_64_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect(lean_object* v_f_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_set_87_; lean_object* v_order_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_111_; 
v_set_87_ = lean_ctor_get(v_a_86_, 0);
v_order_88_ = lean_ctor_get(v_a_86_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_111_ == 0)
{
v___x_90_ = v_a_86_;
v_isShared_91_ = v_isSharedCheck_111_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_order_88_);
lean_inc(v_set_87_);
lean_dec(v_a_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_111_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v_fst_94_; lean_object* v_snd_95_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_92_ = lean_box(0);
v___x_106_ = ((lean_object*)(l_Lean_IR_CollectUsedDecls_collect___redArg___closed__0));
lean_inc(v_set_87_);
lean_inc(v_f_84_);
v___x_107_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_106_, v_f_84_, v_set_87_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_inc(v_f_84_);
v___x_108_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_106_, v_f_84_, v___x_92_, v_set_87_);
v___x_109_ = lean_box(v___x_107_);
v_fst_94_ = v___x_109_;
v_snd_95_ = v___x_108_;
goto v___jp_93_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(v___x_107_);
v_fst_94_ = v___x_110_;
v_snd_95_ = v_set_87_;
goto v___jp_93_;
}
v___jp_93_:
{
uint8_t v___x_96_; 
v___x_96_ = lean_unbox(v_fst_94_);
lean_dec(v_fst_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_array_push(v_order_88_, v_f_84_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_97_);
lean_ctor_set(v___x_90_, 0, v_snd_95_);
v___x_99_ = v___x_90_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_snd_95_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_92_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
return v___x_100_;
}
}
else
{
lean_object* v___x_103_; 
lean_dec(v_f_84_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v_snd_95_);
v___x_103_ = v___x_90_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_snd_95_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_order_88_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_92_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
return v___x_104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collect___boxed(lean_object* v_f_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_IR_CollectUsedDecls_collect(v_f_112_, v_a_113_, v_a_114_);
lean_dec_ref(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(lean_object* v_k_116_, lean_object* v_v_117_, lean_object* v_t_118_){
_start:
{
if (lean_obj_tag(v_t_118_) == 0)
{
lean_object* v_size_119_; lean_object* v_k_120_; lean_object* v_v_121_; lean_object* v_l_122_; lean_object* v_r_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_403_; 
v_size_119_ = lean_ctor_get(v_t_118_, 0);
v_k_120_ = lean_ctor_get(v_t_118_, 1);
v_v_121_ = lean_ctor_get(v_t_118_, 2);
v_l_122_ = lean_ctor_get(v_t_118_, 3);
v_r_123_ = lean_ctor_get(v_t_118_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v_t_118_);
if (v_isSharedCheck_403_ == 0)
{
v___x_125_ = v_t_118_;
v_isShared_126_ = v_isSharedCheck_403_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_r_123_);
lean_inc(v_l_122_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
lean_inc(v_size_119_);
lean_dec(v_t_118_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_403_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___x_127_; 
v___x_127_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_116_, v_k_120_);
switch(v___x_127_)
{
case 0:
{
lean_object* v_impl_128_; lean_object* v___x_129_; 
lean_dec(v_size_119_);
v_impl_128_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_116_, v_v_117_, v_l_122_);
v___x_129_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_123_) == 0)
{
lean_object* v_size_130_; lean_object* v_size_131_; lean_object* v_k_132_; lean_object* v_v_133_; lean_object* v_l_134_; lean_object* v_r_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_size_130_ = lean_ctor_get(v_r_123_, 0);
v_size_131_ = lean_ctor_get(v_impl_128_, 0);
v_k_132_ = lean_ctor_get(v_impl_128_, 1);
v_v_133_ = lean_ctor_get(v_impl_128_, 2);
v_l_134_ = lean_ctor_get(v_impl_128_, 3);
v_r_135_ = lean_ctor_get(v_impl_128_, 4);
lean_inc(v_r_135_);
v___x_136_ = lean_unsigned_to_nat(3u);
v___x_137_ = lean_nat_mul(v___x_136_, v_size_130_);
v___x_138_ = lean_nat_dec_lt(v___x_137_, v_size_131_);
lean_dec(v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
lean_dec(v_r_135_);
v___x_139_ = lean_nat_add(v___x_129_, v_size_131_);
v___x_140_ = lean_nat_add(v___x_139_, v_size_130_);
lean_dec(v___x_139_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 3, v_impl_128_);
lean_ctor_set(v___x_125_, 0, v___x_140_);
v___x_142_ = v___x_125_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_impl_128_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_r_123_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
else
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_209_; 
lean_inc(v_l_134_);
lean_inc(v_v_133_);
lean_inc(v_k_132_);
lean_inc(v_size_131_);
v_isSharedCheck_209_ = !lean_is_exclusive(v_impl_128_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; 
v_unused_210_ = lean_ctor_get(v_impl_128_, 4);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_impl_128_, 3);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_impl_128_, 2);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_impl_128_, 1);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_impl_128_, 0);
lean_dec(v_unused_214_);
v___x_145_ = v_impl_128_;
v_isShared_146_ = v_isSharedCheck_209_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_impl_128_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_209_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_size_147_; lean_object* v_size_148_; lean_object* v_k_149_; lean_object* v_v_150_; lean_object* v_l_151_; lean_object* v_r_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_size_147_ = lean_ctor_get(v_l_134_, 0);
v_size_148_ = lean_ctor_get(v_r_135_, 0);
v_k_149_ = lean_ctor_get(v_r_135_, 1);
v_v_150_ = lean_ctor_get(v_r_135_, 2);
v_l_151_ = lean_ctor_get(v_r_135_, 3);
v_r_152_ = lean_ctor_get(v_r_135_, 4);
v___x_153_ = lean_unsigned_to_nat(2u);
v___x_154_ = lean_nat_mul(v___x_153_, v_size_147_);
v___x_155_ = lean_nat_dec_lt(v_size_148_, v___x_154_);
lean_dec(v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_184_; 
lean_inc(v_r_152_);
lean_inc(v_l_151_);
lean_inc(v_v_150_);
lean_inc(v_k_149_);
v_isSharedCheck_184_ = !lean_is_exclusive(v_r_135_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; 
v_unused_185_ = lean_ctor_get(v_r_135_, 4);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_r_135_, 3);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_r_135_, 2);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_r_135_, 1);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_r_135_, 0);
lean_dec(v_unused_189_);
v___x_157_ = v_r_135_;
v_isShared_158_ = v_isSharedCheck_184_;
goto v_resetjp_156_;
}
else
{
lean_dec(v_r_135_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_184_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___x_172_; lean_object* v___y_174_; 
v___x_159_ = lean_nat_add(v___x_129_, v_size_131_);
lean_dec(v_size_131_);
v___x_160_ = lean_nat_add(v___x_159_, v_size_130_);
lean_dec(v___x_159_);
v___x_172_ = lean_nat_add(v___x_129_, v_size_147_);
if (lean_obj_tag(v_l_151_) == 0)
{
lean_object* v_size_182_; 
v_size_182_ = lean_ctor_get(v_l_151_, 0);
lean_inc(v_size_182_);
v___y_174_ = v_size_182_;
goto v___jp_173_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___y_174_ = v___x_183_;
goto v___jp_173_;
}
v___jp_161_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_nat_add(v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec(v___y_163_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 4, v_r_123_);
lean_ctor_set(v___x_157_, 3, v_r_152_);
lean_ctor_set(v___x_157_, 2, v_v_121_);
lean_ctor_set(v___x_157_, 1, v_k_120_);
lean_ctor_set(v___x_157_, 0, v___x_165_);
v___x_167_ = v___x_157_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_r_152_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_r_123_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_169_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v___x_167_);
lean_ctor_set(v___x_145_, 3, v___y_162_);
lean_ctor_set(v___x_145_, 2, v_v_150_);
lean_ctor_set(v___x_145_, 1, v_k_149_);
lean_ctor_set(v___x_145_, 0, v___x_160_);
v___x_169_ = v___x_145_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_k_149_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_v_150_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v___y_162_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_nat_add(v___x_172_, v___y_174_);
lean_dec(v___y_174_);
lean_dec(v___x_172_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_l_151_);
lean_ctor_set(v___x_125_, 3, v_l_134_);
lean_ctor_set(v___x_125_, 2, v_v_133_);
lean_ctor_set(v___x_125_, 1, v_k_132_);
lean_ctor_set(v___x_125_, 0, v___x_175_);
v___x_177_ = v___x_125_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_132_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_133_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_l_134_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_l_151_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_nat_add(v___x_129_, v_size_130_);
if (lean_obj_tag(v_r_152_) == 0)
{
lean_object* v_size_179_; 
v_size_179_ = lean_ctor_get(v_r_152_, 0);
lean_inc(v_size_179_);
v___y_162_ = v___x_177_;
v___y_163_ = v___x_178_;
v___y_164_ = v_size_179_;
goto v___jp_161_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___y_162_ = v___x_177_;
v___y_163_ = v___x_178_;
v___y_164_ = v___x_180_;
goto v___jp_161_;
}
}
}
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
lean_del_object(v___x_125_);
v___x_190_ = lean_nat_add(v___x_129_, v_size_131_);
lean_dec(v_size_131_);
v___x_191_ = lean_nat_add(v___x_190_, v_size_130_);
lean_dec(v___x_190_);
v___x_192_ = lean_nat_add(v___x_129_, v_size_130_);
v___x_193_ = lean_nat_add(v___x_192_, v_size_148_);
lean_dec(v___x_192_);
lean_inc_ref(v_r_123_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 4, v_r_123_);
lean_ctor_set(v___x_145_, 3, v_r_135_);
lean_ctor_set(v___x_145_, 2, v_v_121_);
lean_ctor_set(v___x_145_, 1, v_k_120_);
lean_ctor_set(v___x_145_, 0, v___x_193_);
v___x_195_ = v___x_145_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_r_135_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_r_123_);
v___x_195_ = v_reuseFailAlloc_208_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_isSharedCheck_202_ = !lean_is_exclusive(v_r_123_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; lean_object* v_unused_205_; lean_object* v_unused_206_; lean_object* v_unused_207_; 
v_unused_203_ = lean_ctor_get(v_r_123_, 4);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_r_123_, 3);
lean_dec(v_unused_204_);
v_unused_205_ = lean_ctor_get(v_r_123_, 2);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_r_123_, 1);
lean_dec(v_unused_206_);
v_unused_207_ = lean_ctor_get(v_r_123_, 0);
lean_dec(v_unused_207_);
v___x_197_ = v_r_123_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_dec(v_r_123_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 4, v___x_195_);
lean_ctor_set(v___x_197_, 3, v_l_134_);
lean_ctor_set(v___x_197_, 2, v_v_133_);
lean_ctor_set(v___x_197_, 1, v_k_132_);
lean_ctor_set(v___x_197_, 0, v___x_191_);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_k_132_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_v_133_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_l_134_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v___x_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_215_; 
v_l_215_ = lean_ctor_get(v_impl_128_, 3);
if (lean_obj_tag(v_l_215_) == 0)
{
lean_object* v_r_216_; lean_object* v_k_217_; lean_object* v_v_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_229_; 
lean_inc_ref(v_l_215_);
v_r_216_ = lean_ctor_get(v_impl_128_, 4);
v_k_217_ = lean_ctor_get(v_impl_128_, 1);
v_v_218_ = lean_ctor_get(v_impl_128_, 2);
v_isSharedCheck_229_ = !lean_is_exclusive(v_impl_128_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_230_ = lean_ctor_get(v_impl_128_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_impl_128_, 0);
lean_dec(v_unused_231_);
v___x_220_ = v_impl_128_;
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_r_216_);
lean_inc(v_v_218_);
lean_inc(v_k_217_);
lean_dec(v_impl_128_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_229_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_216_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 3, v_r_216_);
lean_ctor_set(v___x_220_, 2, v_v_121_);
lean_ctor_set(v___x_220_, 1, v_k_120_);
lean_ctor_set(v___x_220_, 0, v___x_129_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_r_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_r_216_);
v___x_224_ = v_reuseFailAlloc_228_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_226_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v___x_224_);
lean_ctor_set(v___x_125_, 3, v_l_215_);
lean_ctor_set(v___x_125_, 2, v_v_218_);
lean_ctor_set(v___x_125_, 1, v_k_217_);
lean_ctor_set(v___x_125_, 0, v___x_222_);
v___x_226_ = v___x_125_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_217_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_218_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_l_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v_r_232_; 
v_r_232_ = lean_ctor_get(v_impl_128_, 4);
lean_inc(v_r_232_);
if (lean_obj_tag(v_r_232_) == 0)
{
lean_object* v_k_233_; lean_object* v_v_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_257_; 
lean_inc(v_l_215_);
v_k_233_ = lean_ctor_get(v_impl_128_, 1);
v_v_234_ = lean_ctor_get(v_impl_128_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_impl_128_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_258_ = lean_ctor_get(v_impl_128_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_impl_128_, 3);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_impl_128_, 0);
lean_dec(v_unused_260_);
v___x_236_ = v_impl_128_;
v_isShared_237_ = v_isSharedCheck_257_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_v_234_);
lean_inc(v_k_233_);
lean_dec(v_impl_128_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_257_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_k_238_; lean_object* v_v_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_253_; 
v_k_238_ = lean_ctor_get(v_r_232_, 1);
v_v_239_ = lean_ctor_get(v_r_232_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v_r_232_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; 
v_unused_254_ = lean_ctor_get(v_r_232_, 4);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_r_232_, 3);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_r_232_, 0);
lean_dec(v_unused_256_);
v___x_241_ = v_r_232_;
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_v_239_);
lean_inc(v_k_238_);
lean_dec(v_r_232_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_unsigned_to_nat(3u);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 4, v_l_215_);
lean_ctor_set(v___x_241_, 3, v_l_215_);
lean_ctor_set(v___x_241_, 2, v_v_234_);
lean_ctor_set(v___x_241_, 1, v_k_233_);
lean_ctor_set(v___x_241_, 0, v___x_129_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_l_215_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_l_215_);
v___x_245_ = v_reuseFailAlloc_252_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 4, v_l_215_);
lean_ctor_set(v___x_236_, 2, v_v_121_);
lean_ctor_set(v___x_236_, 1, v_k_120_);
lean_ctor_set(v___x_236_, 0, v___x_129_);
v___x_247_ = v___x_236_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_l_215_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_l_215_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v___x_247_);
lean_ctor_set(v___x_125_, 3, v___x_245_);
lean_ctor_set(v___x_125_, 2, v_v_239_);
lean_ctor_set(v___x_125_, 1, v_k_238_);
lean_ctor_set(v___x_125_, 0, v___x_243_);
v___x_249_ = v___x_125_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_k_238_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_v_239_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v___x_247_);
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
}
else
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_unsigned_to_nat(2u);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_r_232_);
lean_ctor_set(v___x_125_, 3, v_impl_128_);
lean_ctor_set(v___x_125_, 0, v___x_261_);
v___x_263_ = v___x_125_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_impl_128_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v_r_232_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
case 1:
{
lean_object* v___x_266_; 
lean_dec(v_v_121_);
lean_dec(v_k_120_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 2, v_v_117_);
lean_ctor_set(v___x_125_, 1, v_k_116_);
v___x_266_ = v___x_125_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_size_119_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_k_116_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v_v_117_);
lean_ctor_set(v_reuseFailAlloc_267_, 3, v_l_122_);
lean_ctor_set(v_reuseFailAlloc_267_, 4, v_r_123_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
default: 
{
lean_object* v_impl_268_; lean_object* v___x_269_; 
lean_dec(v_size_119_);
v_impl_268_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_116_, v_v_117_, v_r_123_);
v___x_269_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_122_) == 0)
{
lean_object* v_size_270_; lean_object* v_size_271_; lean_object* v_k_272_; lean_object* v_v_273_; lean_object* v_l_274_; lean_object* v_r_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_size_270_ = lean_ctor_get(v_l_122_, 0);
v_size_271_ = lean_ctor_get(v_impl_268_, 0);
v_k_272_ = lean_ctor_get(v_impl_268_, 1);
v_v_273_ = lean_ctor_get(v_impl_268_, 2);
v_l_274_ = lean_ctor_get(v_impl_268_, 3);
lean_inc(v_l_274_);
v_r_275_ = lean_ctor_get(v_impl_268_, 4);
v___x_276_ = lean_unsigned_to_nat(3u);
v___x_277_ = lean_nat_mul(v___x_276_, v_size_270_);
v___x_278_ = lean_nat_dec_lt(v___x_277_, v_size_271_);
lean_dec(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
lean_dec(v_l_274_);
v___x_279_ = lean_nat_add(v___x_269_, v_size_270_);
v___x_280_ = lean_nat_add(v___x_279_, v_size_271_);
lean_dec(v___x_279_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_impl_268_);
lean_ctor_set(v___x_125_, 0, v___x_280_);
v___x_282_ = v___x_125_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_l_122_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_impl_268_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
else
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_347_; 
lean_inc(v_r_275_);
lean_inc(v_v_273_);
lean_inc(v_k_272_);
lean_inc(v_size_271_);
v_isSharedCheck_347_ = !lean_is_exclusive(v_impl_268_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_348_ = lean_ctor_get(v_impl_268_, 4);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_impl_268_, 3);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_impl_268_, 2);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_impl_268_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_impl_268_, 0);
lean_dec(v_unused_352_);
v___x_285_ = v_impl_268_;
v_isShared_286_ = v_isSharedCheck_347_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_impl_268_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_347_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_size_287_; lean_object* v_k_288_; lean_object* v_v_289_; lean_object* v_l_290_; lean_object* v_r_291_; lean_object* v_size_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_size_287_ = lean_ctor_get(v_l_274_, 0);
v_k_288_ = lean_ctor_get(v_l_274_, 1);
v_v_289_ = lean_ctor_get(v_l_274_, 2);
v_l_290_ = lean_ctor_get(v_l_274_, 3);
v_r_291_ = lean_ctor_get(v_l_274_, 4);
v_size_292_ = lean_ctor_get(v_r_275_, 0);
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = lean_nat_mul(v___x_293_, v_size_292_);
v___x_295_ = lean_nat_dec_lt(v_size_287_, v___x_294_);
lean_dec(v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_323_; 
lean_inc(v_r_291_);
lean_inc(v_l_290_);
lean_inc(v_v_289_);
lean_inc(v_k_288_);
v_isSharedCheck_323_ = !lean_is_exclusive(v_l_274_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; 
v_unused_324_ = lean_ctor_get(v_l_274_, 4);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_l_274_, 3);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_l_274_, 2);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_l_274_, 1);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_l_274_, 0);
lean_dec(v_unused_328_);
v___x_297_ = v_l_274_;
v_isShared_298_ = v_isSharedCheck_323_;
goto v_resetjp_296_;
}
else
{
lean_dec(v_l_274_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_323_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; lean_object* v___y_313_; 
v___x_299_ = lean_nat_add(v___x_269_, v_size_270_);
v___x_300_ = lean_nat_add(v___x_299_, v_size_271_);
lean_dec(v_size_271_);
if (lean_obj_tag(v_l_290_) == 0)
{
lean_object* v_size_321_; 
v_size_321_ = lean_ctor_get(v_l_290_, 0);
lean_inc(v_size_321_);
v___y_313_ = v_size_321_;
goto v___jp_312_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___y_313_ = v___x_322_;
goto v___jp_312_;
}
v___jp_301_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_nat_add(v___y_302_, v___y_304_);
lean_dec(v___y_304_);
lean_dec(v___y_302_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 4, v_r_275_);
lean_ctor_set(v___x_297_, 3, v_r_291_);
lean_ctor_set(v___x_297_, 2, v_v_273_);
lean_ctor_set(v___x_297_, 1, v_k_272_);
lean_ctor_set(v___x_297_, 0, v___x_305_);
v___x_307_ = v___x_297_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_k_272_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_v_273_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_r_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_r_275_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 4, v___x_307_);
lean_ctor_set(v___x_285_, 3, v___y_303_);
lean_ctor_set(v___x_285_, 2, v_v_289_);
lean_ctor_set(v___x_285_, 1, v_k_288_);
lean_ctor_set(v___x_285_, 0, v___x_300_);
v___x_309_ = v___x_285_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_288_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_289_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___y_303_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = lean_nat_add(v___x_299_, v___y_313_);
lean_dec(v___y_313_);
lean_dec(v___x_299_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_l_290_);
lean_ctor_set(v___x_125_, 0, v___x_314_);
v___x_316_ = v___x_125_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_l_122_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v_l_290_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_nat_add(v___x_269_, v_size_292_);
if (lean_obj_tag(v_r_291_) == 0)
{
lean_object* v_size_318_; 
v_size_318_ = lean_ctor_get(v_r_291_, 0);
lean_inc(v_size_318_);
v___y_302_ = v___x_317_;
v___y_303_ = v___x_316_;
v___y_304_ = v_size_318_;
goto v___jp_301_;
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___y_302_ = v___x_317_;
v___y_303_ = v___x_316_;
v___y_304_ = v___x_319_;
goto v___jp_301_;
}
}
}
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_del_object(v___x_125_);
v___x_329_ = lean_nat_add(v___x_269_, v_size_270_);
v___x_330_ = lean_nat_add(v___x_329_, v_size_271_);
lean_dec(v_size_271_);
v___x_331_ = lean_nat_add(v___x_329_, v_size_287_);
lean_dec(v___x_329_);
lean_inc_ref(v_l_122_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 4, v_l_274_);
lean_ctor_set(v___x_285_, 3, v_l_122_);
lean_ctor_set(v___x_285_, 2, v_v_121_);
lean_ctor_set(v___x_285_, 1, v_k_120_);
lean_ctor_set(v___x_285_, 0, v___x_331_);
v___x_333_ = v___x_285_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_l_122_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_l_274_);
v___x_333_ = v_reuseFailAlloc_346_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_isSharedCheck_340_ = !lean_is_exclusive(v_l_122_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_341_ = lean_ctor_get(v_l_122_, 4);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_l_122_, 3);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_l_122_, 2);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_l_122_, 1);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_l_122_, 0);
lean_dec(v_unused_345_);
v___x_335_ = v_l_122_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_dec(v_l_122_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 4, v_r_275_);
lean_ctor_set(v___x_335_, 3, v___x_333_);
lean_ctor_set(v___x_335_, 2, v_v_273_);
lean_ctor_set(v___x_335_, 1, v_k_272_);
lean_ctor_set(v___x_335_, 0, v___x_330_);
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_k_272_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_v_273_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v_r_275_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_353_; 
v_l_353_ = lean_ctor_get(v_impl_268_, 3);
lean_inc(v_l_353_);
if (lean_obj_tag(v_l_353_) == 0)
{
lean_object* v_r_354_; lean_object* v_k_355_; lean_object* v_v_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_379_; 
v_r_354_ = lean_ctor_get(v_impl_268_, 4);
v_k_355_ = lean_ctor_get(v_impl_268_, 1);
v_v_356_ = lean_ctor_get(v_impl_268_, 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_impl_268_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_380_ = lean_ctor_get(v_impl_268_, 3);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_impl_268_, 0);
lean_dec(v_unused_381_);
v___x_358_ = v_impl_268_;
v_isShared_359_ = v_isSharedCheck_379_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_r_354_);
lean_inc(v_v_356_);
lean_inc(v_k_355_);
lean_dec(v_impl_268_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_379_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_375_; 
v_k_360_ = lean_ctor_get(v_l_353_, 1);
v_v_361_ = lean_ctor_get(v_l_353_, 2);
v_isSharedCheck_375_ = !lean_is_exclusive(v_l_353_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; lean_object* v_unused_378_; 
v_unused_376_ = lean_ctor_get(v_l_353_, 4);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_l_353_, 3);
lean_dec(v_unused_377_);
v_unused_378_ = lean_ctor_get(v_l_353_, 0);
lean_dec(v_unused_378_);
v___x_363_ = v_l_353_;
v_isShared_364_ = v_isSharedCheck_375_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_v_361_);
lean_inc(v_k_360_);
lean_dec(v_l_353_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_375_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_354_, 2);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 4, v_r_354_);
lean_ctor_set(v___x_363_, 3, v_r_354_);
lean_ctor_set(v___x_363_, 2, v_v_121_);
lean_ctor_set(v___x_363_, 1, v_k_120_);
lean_ctor_set(v___x_363_, 0, v___x_269_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_r_354_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_r_354_);
v___x_367_ = v_reuseFailAlloc_374_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
lean_inc(v_r_354_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 3, v_r_354_);
lean_ctor_set(v___x_358_, 0, v___x_269_);
v___x_369_ = v___x_358_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_r_354_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_r_354_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v___x_369_);
lean_ctor_set(v___x_125_, 3, v___x_367_);
lean_ctor_set(v___x_125_, 2, v_v_361_);
lean_ctor_set(v___x_125_, 1, v_k_360_);
lean_ctor_set(v___x_125_, 0, v___x_365_);
v___x_371_ = v___x_125_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
else
{
lean_object* v_r_382_; 
v_r_382_ = lean_ctor_get(v_impl_268_, 4);
lean_inc(v_r_382_);
if (lean_obj_tag(v_r_382_) == 0)
{
lean_object* v_k_383_; lean_object* v_v_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_395_; 
v_k_383_ = lean_ctor_get(v_impl_268_, 1);
v_v_384_ = lean_ctor_get(v_impl_268_, 2);
v_isSharedCheck_395_ = !lean_is_exclusive(v_impl_268_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; 
v_unused_396_ = lean_ctor_get(v_impl_268_, 4);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_impl_268_, 3);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_impl_268_, 0);
lean_dec(v_unused_398_);
v___x_386_ = v_impl_268_;
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_v_384_);
lean_inc(v_k_383_);
lean_dec(v_impl_268_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(3u);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v_l_353_);
lean_ctor_set(v___x_386_, 2, v_v_121_);
lean_ctor_set(v___x_386_, 1, v_k_120_);
lean_ctor_set(v___x_386_, 0, v___x_269_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_l_353_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_l_353_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_r_382_);
lean_ctor_set(v___x_125_, 3, v___x_390_);
lean_ctor_set(v___x_125_, 2, v_v_384_);
lean_ctor_set(v___x_125_, 1, v_k_383_);
lean_ctor_set(v___x_125_, 0, v___x_388_);
v___x_392_ = v___x_125_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_k_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_v_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_r_382_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_unsigned_to_nat(2u);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 4, v_impl_268_);
lean_ctor_set(v___x_125_, 3, v_r_382_);
lean_ctor_set(v___x_125_, 0, v___x_399_);
v___x_401_ = v___x_125_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_120_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_v_121_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_r_382_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_impl_268_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
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
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_k_116_);
lean_ctor_set(v___x_405_, 2, v_v_117_);
lean_ctor_set(v___x_405_, 3, v_t_118_);
lean_ctor_set(v___x_405_, 4, v_t_118_);
return v___x_405_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(lean_object* v_k_406_, lean_object* v_t_407_){
_start:
{
if (lean_obj_tag(v_t_407_) == 0)
{
lean_object* v_k_408_; lean_object* v_l_409_; lean_object* v_r_410_; uint8_t v___x_411_; 
v_k_408_ = lean_ctor_get(v_t_407_, 1);
v_l_409_ = lean_ctor_get(v_t_407_, 3);
v_r_410_ = lean_ctor_get(v_t_407_, 4);
v___x_411_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_406_, v_k_408_);
switch(v___x_411_)
{
case 0:
{
v_t_407_ = v_l_409_;
goto _start;
}
case 1:
{
uint8_t v___x_413_; 
v___x_413_ = 1;
return v___x_413_;
}
default: 
{
v_t_407_ = v_r_410_;
goto _start;
}
}
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg___boxed(lean_object* v_k_416_, lean_object* v_t_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_416_, v_t_417_);
lean_dec(v_t_417_);
lean_dec(v_k_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody(lean_object* v_x_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
switch(lean_obj_tag(v_x_420_))
{
case 6:
{
lean_object* v_b_423_; lean_object* v_c_424_; lean_object* v_set_425_; lean_object* v_order_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_448_; 
v_b_423_ = lean_ctor_get(v_x_420_, 1);
lean_inc(v_b_423_);
v_c_424_ = lean_ctor_get(v_x_420_, 3);
lean_inc(v_c_424_);
lean_dec_ref_known(v_x_420_, 5);
v_set_425_ = lean_ctor_get(v_a_422_, 0);
v_order_426_ = lean_ctor_get(v_a_422_, 1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_448_ == 0)
{
v___x_428_ = v_a_422_;
v_isShared_429_ = v_isSharedCheck_448_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_order_426_);
lean_inc(v_set_425_);
lean_dec(v_a_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_448_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_fst_431_; lean_object* v_snd_432_; uint8_t v___x_443_; 
v___x_443_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_c_424_, v_set_425_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_box(0);
lean_inc(v_c_424_);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_c_424_, v___x_444_, v_set_425_);
v___x_446_ = lean_box(v___x_443_);
v_fst_431_ = v___x_446_;
v_snd_432_ = v___x_445_;
goto v___jp_430_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_box(v___x_443_);
v_fst_431_ = v___x_447_;
v_snd_432_ = v_set_425_;
goto v___jp_430_;
}
v___jp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_unbox(v_fst_431_);
lean_dec(v_fst_431_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_array_push(v_order_426_, v_c_424_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_434_);
lean_ctor_set(v___x_428_, 0, v_snd_432_);
v___x_436_ = v___x_428_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_snd_432_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v_x_420_ = v_b_423_;
v_a_422_ = v___x_436_;
goto _start;
}
}
else
{
lean_object* v___x_440_; 
lean_dec(v_c_424_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_snd_432_);
v___x_440_ = v___x_428_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_snd_432_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_order_426_);
v___x_440_ = v_reuseFailAlloc_442_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v_x_420_ = v_b_423_;
v_a_422_ = v___x_440_;
goto _start;
}
}
}
}
}
case 7:
{
lean_object* v_b_449_; lean_object* v_c_450_; lean_object* v_set_451_; lean_object* v_order_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_474_; 
v_b_449_ = lean_ctor_get(v_x_420_, 1);
lean_inc(v_b_449_);
v_c_450_ = lean_ctor_get(v_x_420_, 2);
lean_inc(v_c_450_);
lean_dec_ref_known(v_x_420_, 4);
v_set_451_ = lean_ctor_get(v_a_422_, 0);
v_order_452_ = lean_ctor_get(v_a_422_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_474_ == 0)
{
v___x_454_ = v_a_422_;
v_isShared_455_ = v_isSharedCheck_474_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_order_452_);
lean_inc(v_set_451_);
lean_dec(v_a_422_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_474_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_fst_457_; lean_object* v_snd_458_; uint8_t v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_c_450_, v_set_451_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
lean_inc(v_c_450_);
v___x_471_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_c_450_, v___x_470_, v_set_451_);
v___x_472_ = lean_box(v___x_469_);
v_fst_457_ = v___x_472_;
v_snd_458_ = v___x_471_;
goto v___jp_456_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(v___x_469_);
v_fst_457_ = v___x_473_;
v_snd_458_ = v_set_451_;
goto v___jp_456_;
}
v___jp_456_:
{
uint8_t v___x_459_; 
v___x_459_ = lean_unbox(v_fst_457_);
lean_dec(v_fst_457_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_array_push(v_order_452_, v_c_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_460_);
lean_ctor_set(v___x_454_, 0, v_snd_458_);
v___x_462_ = v___x_454_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_snd_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_464_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_x_420_ = v_b_449_;
v_a_422_ = v___x_462_;
goto _start;
}
}
else
{
lean_object* v___x_466_; 
lean_dec(v_c_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v_snd_458_);
v___x_466_ = v___x_454_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_snd_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_order_452_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v_x_420_ = v_b_449_;
v_a_422_ = v___x_466_;
goto _start;
}
}
}
}
}
case 19:
{
lean_object* v_v_475_; lean_object* v_b_476_; lean_object* v___x_477_; lean_object* v_snd_478_; 
v_v_475_ = lean_ctor_get(v_x_420_, 2);
lean_inc(v_v_475_);
v_b_476_ = lean_ctor_get(v_x_420_, 3);
lean_inc(v_b_476_);
lean_dec_ref_known(v_x_420_, 4);
v___x_477_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_v_475_, v_a_421_, v_a_422_);
v_snd_478_ = lean_ctor_get(v___x_477_, 1);
lean_inc(v_snd_478_);
lean_dec_ref(v___x_477_);
v_x_420_ = v_b_476_;
v_a_422_ = v_snd_478_;
goto _start;
}
case 27:
{
lean_object* v_cs_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_cs_480_ = lean_ctor_get(v_x_420_, 3);
lean_inc_ref(v_cs_480_);
lean_dec_ref_known(v_x_420_, 4);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_array_get_size(v_cs_480_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_nat_dec_lt(v___x_481_, v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec_ref(v_cs_480_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v_a_422_);
return v___x_485_;
}
else
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_le(v___x_482_, v___x_482_);
if (v___x_486_ == 0)
{
if (v___x_484_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_cs_480_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_483_);
lean_ctor_set(v___x_487_, 1, v_a_422_);
return v___x_487_;
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((size_t)0ULL);
v___x_489_ = lean_usize_of_nat(v___x_482_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_480_, v___x_488_, v___x_489_, v___x_483_, v_a_421_, v_a_422_);
lean_dec_ref(v_cs_480_);
return v___x_490_;
}
}
else
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((size_t)0ULL);
v___x_492_ = lean_usize_of_nat(v___x_482_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_cs_480_, v___x_491_, v___x_492_, v___x_483_, v_a_421_, v_a_422_);
lean_dec_ref(v_cs_480_);
return v___x_493_;
}
}
}
default: 
{
uint8_t v___x_494_; 
v___x_494_ = l_Lean_IR_FnBody_isTerminal(v_x_420_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_IR_FnBody_body(v_x_420_);
lean_dec(v_x_420_);
v_x_420_ = v___x_495_;
goto _start;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_x_420_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_422_);
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(lean_object* v_as_499_, size_t v_i_500_, size_t v_stop_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_eq(v_i_500_, v_stop_501_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; size_t v___x_511_; size_t v___x_512_; 
v___x_506_ = lean_array_uget_borrowed(v_as_499_, v_i_500_);
v___x_507_ = l_Lean_IR_Alt_body(v___x_506_);
v___x_508_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v___x_507_, v___y_503_, v___y_504_);
v_fst_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v___x_508_, 1);
lean_inc(v_snd_510_);
lean_dec_ref(v___x_508_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_500_, v___x_511_);
v_i_500_ = v___x_512_;
v_b_502_ = v_fst_509_;
v___y_504_ = v_snd_510_;
goto _start;
}
else
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_b_502_);
lean_ctor_set(v___x_514_, 1, v___y_504_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2___boxed(lean_object* v_as_515_, lean_object* v_i_516_, lean_object* v_stop_517_, lean_object* v_b_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
size_t v_i_boxed_521_; size_t v_stop_boxed_522_; lean_object* v_res_523_; 
v_i_boxed_521_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_stop_boxed_522_ = lean_unbox_usize(v_stop_517_);
lean_dec(v_stop_517_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__2(v_as_515_, v_i_boxed_521_, v_stop_boxed_522_, v_b_518_, v___y_519_, v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_as_515_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectFnBody___boxed(lean_object* v_x_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_x_524_, v_a_525_, v_a_526_);
lean_dec_ref(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(lean_object* v_00_u03b2_528_, lean_object* v_k_529_, lean_object* v_t_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_k_529_, v_t_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_532_, lean_object* v_k_533_, lean_object* v_t_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0(v_00_u03b2_532_, v_k_533_, v_t_534_);
lean_dec(v_t_534_);
lean_dec(v_k_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1(lean_object* v_00_u03b2_537_, lean_object* v_k_538_, lean_object* v_v_539_, lean_object* v_t_540_, lean_object* v_hl_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_k_538_, v_v_539_, v_t_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl(lean_object* v_fn_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
lean_inc_ref(v_a_544_);
v___x_546_ = lean_get_init_fn_name_for(v_a_544_, v_fn_543_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v_set_548_; lean_object* v_order_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_571_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v___x_546_, 1);
v_set_548_ = lean_ctor_get(v_a_545_, 0);
v_order_549_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_571_ == 0)
{
v___x_551_ = v_a_545_;
v_isShared_552_ = v_isSharedCheck_571_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_order_549_);
lean_inc(v_set_548_);
lean_dec(v_a_545_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_571_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v_fst_555_; lean_object* v_snd_556_; uint8_t v___x_567_; 
v___x_553_ = lean_box(0);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v_val_547_, v_set_548_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc(v_val_547_);
v___x_568_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v_val_547_, v___x_553_, v_set_548_);
v___x_569_ = lean_box(v___x_567_);
v_fst_555_ = v___x_569_;
v_snd_556_ = v___x_568_;
goto v___jp_554_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_box(v___x_567_);
v_fst_555_ = v___x_570_;
v_snd_556_ = v_set_548_;
goto v___jp_554_;
}
v___jp_554_:
{
uint8_t v___x_557_; 
v___x_557_ = lean_unbox(v_fst_555_);
lean_dec(v_fst_555_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_array_push(v_order_549_, v_val_547_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v___x_558_);
lean_ctor_set(v___x_551_, 0, v_snd_556_);
v___x_560_ = v___x_551_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_snd_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_553_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
else
{
lean_object* v___x_564_; 
lean_dec(v_val_547_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_snd_556_);
v___x_564_ = v___x_551_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_snd_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_order_549_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_553_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
}
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v___x_546_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_a_545_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectInitDecl___boxed(lean_object* v_fn_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_fn_574_, v_a_575_, v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl(lean_object* v_x_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v_f_581_; lean_object* v_body_582_; lean_object* v___x_583_; lean_object* v_snd_584_; lean_object* v___x_585_; 
v_f_581_ = lean_ctor_get(v_x_578_, 0);
lean_inc(v_f_581_);
v_body_582_ = lean_ctor_get(v_x_578_, 3);
lean_inc(v_body_582_);
lean_dec_ref_known(v_x_578_, 5);
v___x_583_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_581_, v_a_579_, v_a_580_);
v_snd_584_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_584_);
lean_dec_ref(v___x_583_);
v___x_585_ = l_Lean_IR_CollectUsedDecls_collectFnBody(v_body_582_, v_a_579_, v_snd_584_);
return v___x_585_;
}
else
{
lean_object* v_f_586_; lean_object* v___x_587_; 
v_f_586_ = lean_ctor_get(v_x_578_, 0);
lean_inc(v_f_586_);
lean_dec_ref_known(v_x_578_, 4);
v___x_587_ = l_Lean_IR_CollectUsedDecls_collectInitDecl(v_f_586_, v_a_579_, v_a_580_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDecl___boxed(lean_object* v_x_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_x_588_, v_a_589_, v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(lean_object* v_as_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
if (lean_obj_tag(v_as_592_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___y_594_);
return v___x_596_;
}
else
{
lean_object* v_head_597_; lean_object* v_tail_598_; lean_object* v___x_599_; lean_object* v_snd_600_; lean_object* v_set_601_; lean_object* v_order_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_625_; 
v_head_597_ = lean_ctor_get(v_as_592_, 0);
lean_inc_n(v_head_597_, 2);
v_tail_598_ = lean_ctor_get(v_as_592_, 1);
lean_inc(v_tail_598_);
lean_dec_ref_known(v_as_592_, 2);
v___x_599_ = l_Lean_IR_CollectUsedDecls_collectDecl(v_head_597_, v___y_593_, v___y_594_);
v_snd_600_ = lean_ctor_get(v___x_599_, 1);
lean_inc(v_snd_600_);
lean_dec_ref(v___x_599_);
v_set_601_ = lean_ctor_get(v_snd_600_, 0);
v_order_602_ = lean_ctor_get(v_snd_600_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_snd_600_);
if (v_isSharedCheck_625_ == 0)
{
v___x_604_ = v_snd_600_;
v_isShared_605_ = v_isSharedCheck_625_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_order_602_);
lean_inc(v_set_601_);
lean_dec(v_snd_600_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_625_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v_fst_608_; lean_object* v_snd_609_; uint8_t v___x_620_; 
v___x_606_ = l_Lean_IR_Decl_name(v_head_597_);
lean_dec(v_head_597_);
v___x_620_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__0___redArg(v___x_606_, v_set_601_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_box(0);
lean_inc(v___x_606_);
v___x_622_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_CollectUsedDecls_collectFnBody_spec__1___redArg(v___x_606_, v___x_621_, v_set_601_);
v___x_623_ = lean_box(v___x_620_);
v_fst_608_ = v___x_623_;
v_snd_609_ = v___x_622_;
goto v___jp_607_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_box(v___x_620_);
v_fst_608_ = v___x_624_;
v_snd_609_ = v_set_601_;
goto v___jp_607_;
}
v___jp_607_:
{
uint8_t v___x_610_; 
v___x_610_ = lean_unbox(v_fst_608_);
lean_dec(v_fst_608_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_array_push(v_order_602_, v___x_606_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_611_);
lean_ctor_set(v___x_604_, 0, v_snd_609_);
v___x_613_ = v___x_604_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_snd_609_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v_as_592_ = v_tail_598_;
v___y_594_ = v___x_613_;
goto _start;
}
}
else
{
lean_object* v___x_617_; 
lean_dec(v___x_606_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_snd_609_);
v___x_617_ = v___x_604_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_snd_609_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_order_602_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v_as_592_ = v_tail_598_;
v___y_594_ = v___x_617_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0___boxed(lean_object* v_as_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_as_626_, v___y_627_, v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop(lean_object* v_decls_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_630_, v_a_631_, v_a_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectUsedDecls_collectDeclLoop___boxed(lean_object* v_decls_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_IR_CollectUsedDecls_collectDeclLoop(v_decls_634_, v_a_635_, v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_IR_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l_Lean_IR_collectUsedDecls___closed__0));
v___x_641_ = l_Lean_NameSet_empty;
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls(lean_object* v_env_643_, lean_object* v_decls_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_snd_647_; lean_object* v_order_648_; 
v___x_645_ = lean_obj_once(&l_Lean_IR_collectUsedDecls___closed__1, &l_Lean_IR_collectUsedDecls___closed__1_once, _init_l_Lean_IR_collectUsedDecls___closed__1);
v___x_646_ = l_List_forM___at___00Lean_IR_CollectUsedDecls_collectDeclLoop_spec__0(v_decls_644_, v_env_643_, v___x_645_);
v_snd_647_ = lean_ctor_get(v___x_646_, 1);
lean_inc(v_snd_647_);
lean_dec_ref(v___x_646_);
v_order_648_ = lean_ctor_get(v_snd_647_, 1);
lean_inc_ref(v_order_648_);
lean_dec(v_snd_647_);
return v_order_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_collectUsedDecls___boxed(lean_object* v_env_649_, lean_object* v_decls_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_IR_collectUsedDecls(v_env_649_, v_decls_650_);
lean_dec_ref(v_env_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectVar(lean_object* v_x_654_, lean_object* v_t_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v_fst_657_ = lean_ctor_get(v_x_656_, 0);
v_snd_658_ = lean_ctor_get(v_x_656_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_668_ == 0)
{
v___x_660_ = v_x_656_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v_x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_662_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_663_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_662_, v___x_663_, v_fst_657_, v_x_654_, v_t_655_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_snd_658_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
return v_x_669_;
}
else
{
lean_object* v_key_671_; lean_object* v_value_672_; lean_object* v_tail_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_696_; 
v_key_671_ = lean_ctor_get(v_x_670_, 0);
v_value_672_ = lean_ctor_get(v_x_670_, 1);
v_tail_673_ = lean_ctor_get(v_x_670_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_696_ == 0)
{
v___x_675_ = v_x_670_;
v_isShared_676_ = v_isSharedCheck_696_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_tail_673_);
lean_inc(v_value_672_);
lean_inc(v_key_671_);
lean_dec(v_x_670_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_696_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v_fold_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_677_ = lean_array_get_size(v_x_669_);
v___x_678_ = l_Lean_IR_instHashableVarId_hash(v_key_671_);
v___x_679_ = 32ULL;
v___x_680_ = lean_uint64_shift_right(v___x_678_, v___x_679_);
v_fold_681_ = lean_uint64_xor(v___x_678_, v___x_680_);
v___x_682_ = 16ULL;
v___x_683_ = lean_uint64_shift_right(v_fold_681_, v___x_682_);
v___x_684_ = lean_uint64_xor(v_fold_681_, v___x_683_);
v___x_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = lean_usize_of_nat(v___x_677_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_sub(v___x_686_, v___x_687_);
v___x_689_ = lean_usize_land(v___x_685_, v___x_688_);
v___x_690_ = lean_array_uget_borrowed(v_x_669_, v___x_689_);
lean_inc(v___x_690_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 2, v___x_690_);
v___x_692_ = v___x_675_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_key_671_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_value_672_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v___x_690_);
v___x_692_ = v_reuseFailAlloc_695_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_array_uset(v_x_669_, v___x_689_, v___x_692_);
v_x_669_ = v___x_693_;
v_x_670_ = v_tail_673_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(lean_object* v_i_697_, lean_object* v_source_698_, lean_object* v_target_699_){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_array_get_size(v_source_698_);
v___x_701_ = lean_nat_dec_lt(v_i_697_, v___x_700_);
if (v___x_701_ == 0)
{
lean_dec_ref(v_source_698_);
lean_dec(v_i_697_);
return v_target_699_;
}
else
{
lean_object* v_es_702_; lean_object* v___x_703_; lean_object* v_source_704_; lean_object* v_target_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_es_702_ = lean_array_fget(v_source_698_, v_i_697_);
v___x_703_ = lean_box(0);
v_source_704_ = lean_array_fset(v_source_698_, v_i_697_, v___x_703_);
v_target_705_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_target_699_, v_es_702_);
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_i_697_, v___x_706_);
lean_dec(v_i_697_);
v_i_697_ = v___x_707_;
v_source_698_ = v_source_704_;
v_target_699_ = v_target_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(lean_object* v_data_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_nbuckets_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_710_ = lean_array_get_size(v_data_709_);
v___x_711_ = lean_unsigned_to_nat(2u);
v_nbuckets_712_ = lean_nat_mul(v___x_710_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_box(0);
v___x_715_ = lean_mk_array(v_nbuckets_712_, v___x_714_);
v___x_716_ = lean_array_propagate_mark(v_data_709_, v___x_715_);
v___x_717_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v___x_713_, v_data_709_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_a_718_, lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_719_) == 0)
{
uint8_t v___x_720_; 
v___x_720_ = 0;
return v___x_720_;
}
else
{
lean_object* v_key_721_; lean_object* v_tail_722_; uint8_t v___x_723_; 
v_key_721_ = lean_ctor_get(v_x_719_, 0);
v_tail_722_ = lean_ctor_get(v_x_719_, 2);
v___x_723_ = l_Lean_IR_instBEqVarId_beq(v_key_721_, v_a_718_);
if (v___x_723_ == 0)
{
v_x_719_ = v_tail_722_;
goto _start;
}
else
{
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_a_725_, lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_725_, v_x_726_);
lean_dec(v_x_726_);
lean_dec(v_a_725_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(lean_object* v_a_729_, lean_object* v_b_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_dec(v_b_730_);
lean_dec(v_a_729_);
return v_x_731_;
}
else
{
lean_object* v_key_732_; lean_object* v_value_733_; lean_object* v_tail_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_746_; 
v_key_732_ = lean_ctor_get(v_x_731_, 0);
v_value_733_ = lean_ctor_get(v_x_731_, 1);
v_tail_734_ = lean_ctor_get(v_x_731_, 2);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_746_ == 0)
{
v___x_736_ = v_x_731_;
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_tail_734_);
lean_inc(v_value_733_);
lean_inc(v_key_732_);
lean_dec(v_x_731_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_746_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; 
v___x_738_ = l_Lean_IR_instBEqVarId_beq(v_key_732_, v_a_729_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_729_, v_b_730_, v_tail_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 2, v___x_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_key_732_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_value_733_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_744_; 
lean_dec(v_value_733_);
lean_dec(v_key_732_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_b_730_);
lean_ctor_set(v___x_736_, 0, v_a_729_);
v___x_744_ = v___x_736_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_729_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_b_730_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_tail_734_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_747_, lean_object* v_a_748_, lean_object* v_b_749_){
_start:
{
lean_object* v_size_750_; lean_object* v_buckets_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_794_; 
v_size_750_ = lean_ctor_get(v_m_747_, 0);
v_buckets_751_ = lean_ctor_get(v_m_747_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_m_747_);
if (v_isSharedCheck_794_ == 0)
{
v___x_753_ = v_m_747_;
v_isShared_754_ = v_isSharedCheck_794_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_buckets_751_);
lean_inc(v_size_750_);
lean_dec(v_m_747_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_794_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v_fold_759_; uint64_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v_bkt_768_; uint8_t v___x_769_; 
v___x_755_ = lean_array_get_size(v_buckets_751_);
v___x_756_ = l_Lean_IR_instHashableVarId_hash(v_a_748_);
v___x_757_ = 32ULL;
v___x_758_ = lean_uint64_shift_right(v___x_756_, v___x_757_);
v_fold_759_ = lean_uint64_xor(v___x_756_, v___x_758_);
v___x_760_ = 16ULL;
v___x_761_ = lean_uint64_shift_right(v_fold_759_, v___x_760_);
v___x_762_ = lean_uint64_xor(v_fold_759_, v___x_761_);
v___x_763_ = lean_uint64_to_usize(v___x_762_);
v___x_764_ = lean_usize_of_nat(v___x_755_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_sub(v___x_764_, v___x_765_);
v___x_767_ = lean_usize_land(v___x_763_, v___x_766_);
v_bkt_768_ = lean_array_uget_borrowed(v_buckets_751_, v___x_767_);
v___x_769_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_748_, v_bkt_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v_size_x27_771_; lean_object* v___x_772_; lean_object* v_buckets_x27_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v_size_x27_771_ = lean_nat_add(v_size_750_, v___x_770_);
lean_dec(v_size_750_);
lean_inc(v_bkt_768_);
v___x_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_772_, 0, v_a_748_);
lean_ctor_set(v___x_772_, 1, v_b_749_);
lean_ctor_set(v___x_772_, 2, v_bkt_768_);
v_buckets_x27_773_ = lean_array_uset(v_buckets_751_, v___x_767_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(4u);
v___x_775_ = lean_nat_mul(v_size_x27_771_, v___x_774_);
v___x_776_ = lean_unsigned_to_nat(3u);
v___x_777_ = lean_nat_div(v___x_775_, v___x_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_array_get_size(v_buckets_x27_773_);
v___x_779_ = lean_nat_dec_le(v___x_777_, v___x_778_);
lean_dec(v___x_777_);
if (v___x_779_ == 0)
{
lean_object* v_val_780_; lean_object* v___x_782_; 
v_val_780_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_buckets_x27_773_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v_val_780_);
lean_ctor_set(v___x_753_, 0, v_size_x27_771_);
v___x_782_ = v___x_753_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_size_x27_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_val_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v___x_785_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v_buckets_x27_773_);
lean_ctor_set(v___x_753_, 0, v_size_x27_771_);
v___x_785_ = v___x_753_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_size_x27_771_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_buckets_x27_773_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v___x_787_; lean_object* v_buckets_x27_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_inc(v_bkt_768_);
v___x_787_ = lean_box(0);
v_buckets_x27_788_ = lean_array_uset(v_buckets_751_, v___x_767_, v___x_787_);
v___x_789_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_748_, v_b_749_, v_bkt_768_);
v___x_790_ = lean_array_uset(v_buckets_x27_788_, v___x_767_, v___x_789_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v___x_790_);
v___x_792_ = v___x_753_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_size_750_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_as_795_, size_t v_i_796_, size_t v_stop_797_, lean_object* v_b_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_796_, v_stop_797_);
if (v___x_799_ == 0)
{
lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_815_; 
v_fst_800_ = lean_ctor_get(v_b_798_, 0);
v_snd_801_ = lean_ctor_get(v_b_798_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_b_798_);
if (v_isSharedCheck_815_ == 0)
{
v___x_803_ = v_b_798_;
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_inc(v_fst_800_);
lean_dec(v_b_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v_x_806_; lean_object* v_ty_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_805_ = lean_array_uget_borrowed(v_as_795_, v_i_796_);
v_x_806_ = lean_ctor_get(v___x_805_, 0);
v_ty_807_ = lean_ctor_get(v___x_805_, 1);
lean_inc(v_ty_807_);
lean_inc(v_x_806_);
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_800_, v_x_806_, v_ty_807_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_808_);
v___x_810_ = v___x_803_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_snd_801_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
size_t v___x_811_; size_t v___x_812_; 
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_add(v_i_796_, v___x_811_);
v_i_796_ = v___x_812_;
v_b_798_ = v___x_810_;
goto _start;
}
}
}
else
{
return v_b_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_as_816_, lean_object* v_i_817_, lean_object* v_stop_818_, lean_object* v_b_819_){
_start:
{
size_t v_i_boxed_820_; size_t v_stop_boxed_821_; lean_object* v_res_822_; 
v_i_boxed_820_ = lean_unbox_usize(v_i_817_);
lean_dec(v_i_817_);
v_stop_boxed_821_ = lean_unbox_usize(v_stop_818_);
lean_dec(v_stop_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_as_816_, v_i_boxed_820_, v_stop_boxed_821_, v_b_819_);
lean_dec_ref(v_as_816_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_823_, lean_object* v_s_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_array_get_size(v_ps_823_);
v___x_827_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
return v_s_824_;
}
else
{
uint8_t v___x_828_; 
v___x_828_ = lean_nat_dec_le(v___x_826_, v___x_826_);
if (v___x_828_ == 0)
{
if (v___x_827_ == 0)
{
return v_s_824_;
}
else
{
size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_826_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_823_, v___x_829_, v___x_830_, v_s_824_);
return v___x_831_;
}
}
else
{
size_t v___x_832_; size_t v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((size_t)0ULL);
v___x_833_ = lean_usize_of_nat(v___x_826_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_ps_823_, v___x_832_, v___x_833_, v_s_824_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_835_, lean_object* v_s_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_IR_CollectMaps_collectParams(v_ps_835_, v_s_836_);
lean_dec_ref(v_ps_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_838_, lean_object* v_m_839_, lean_object* v_a_840_, lean_object* v_b_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_839_, v_a_840_, v_b_841_);
return v___x_842_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_843_, lean_object* v_a_844_, lean_object* v_x_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_a_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_847_, lean_object* v_a_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_847_, v_a_848_, v_x_849_);
lean_dec(v_x_849_);
lean_dec(v_a_848_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1(lean_object* v_00_u03b2_852_, lean_object* v_data_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1___redArg(v_data_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2(lean_object* v_00_u03b2_855_, lean_object* v_a_856_, lean_object* v_b_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__2___redArg(v_a_856_, v_b_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_860_, lean_object* v_i_861_, lean_object* v_source_862_, lean_object* v_target_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2___redArg(v_i_861_, v_source_862_, v_target_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__1_spec__2_spec__4___redArg(v_x_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_871_, lean_object* v_xs_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_885_; 
v_fst_874_ = lean_ctor_get(v_x_873_, 0);
v_snd_875_ = lean_ctor_get(v_x_873_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_885_ == 0)
{
v___x_877_ = v_x_873_;
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snd_875_);
lean_inc(v_fst_874_);
lean_dec(v_x_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_885_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_879_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_880_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_879_, v___x_880_, v_snd_875_, v_j_871_, v_xs_872_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_fst_874_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
uint8_t v___x_888_; 
v___x_888_ = 0;
return v___x_888_;
}
else
{
lean_object* v_key_889_; lean_object* v_tail_890_; uint8_t v___x_891_; 
v_key_889_ = lean_ctor_get(v_x_887_, 0);
v_tail_890_ = lean_ctor_get(v_x_887_, 2);
v___x_891_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_889_, v_a_886_);
if (v___x_891_ == 0)
{
v_x_887_ = v_tail_890_;
goto _start;
}
else
{
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_a_893_, lean_object* v_x_894_){
_start:
{
uint8_t v_res_895_; lean_object* v_r_896_; 
v_res_895_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_893_, v_x_894_);
lean_dec(v_x_894_);
lean_dec(v_a_893_);
v_r_896_ = lean_box(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
return v_x_897_;
}
else
{
lean_object* v_key_899_; lean_object* v_value_900_; lean_object* v_tail_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_924_; 
v_key_899_ = lean_ctor_get(v_x_898_, 0);
v_value_900_ = lean_ctor_get(v_x_898_, 1);
v_tail_901_ = lean_ctor_get(v_x_898_, 2);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_924_ == 0)
{
v___x_903_ = v_x_898_;
v_isShared_904_ = v_isSharedCheck_924_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_tail_901_);
lean_inc(v_value_900_);
lean_inc(v_key_899_);
lean_dec(v_x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_924_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v_fold_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_905_ = lean_array_get_size(v_x_897_);
v___x_906_ = l_Lean_IR_instHashableJoinPointId_hash(v_key_899_);
v___x_907_ = 32ULL;
v___x_908_ = lean_uint64_shift_right(v___x_906_, v___x_907_);
v_fold_909_ = lean_uint64_xor(v___x_906_, v___x_908_);
v___x_910_ = 16ULL;
v___x_911_ = lean_uint64_shift_right(v_fold_909_, v___x_910_);
v___x_912_ = lean_uint64_xor(v_fold_909_, v___x_911_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = lean_usize_of_nat(v___x_905_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_land(v___x_913_, v___x_916_);
v___x_918_ = lean_array_uget_borrowed(v_x_897_, v___x_917_);
lean_inc(v___x_918_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_918_);
v___x_920_ = v___x_903_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_key_899_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_value_900_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v___x_918_);
v___x_920_ = v_reuseFailAlloc_923_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_array_uset(v_x_897_, v___x_917_, v___x_920_);
v_x_897_ = v___x_921_;
v_x_898_ = v_tail_901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(lean_object* v_i_925_, lean_object* v_source_926_, lean_object* v_target_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_get_size(v_source_926_);
v___x_929_ = lean_nat_dec_lt(v_i_925_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec_ref(v_source_926_);
lean_dec(v_i_925_);
return v_target_927_;
}
else
{
lean_object* v_es_930_; lean_object* v___x_931_; lean_object* v_source_932_; lean_object* v_target_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_es_930_ = lean_array_fget(v_source_926_, v_i_925_);
v___x_931_ = lean_box(0);
v_source_932_ = lean_array_fset(v_source_926_, v_i_925_, v___x_931_);
v_target_933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_target_927_, v_es_930_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_i_925_, v___x_934_);
lean_dec(v_i_925_);
v_i_925_ = v___x_935_;
v_source_926_ = v_source_932_;
v_target_927_ = v_target_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(lean_object* v_data_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_nbuckets_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_938_ = lean_array_get_size(v_data_937_);
v___x_939_ = lean_unsigned_to_nat(2u);
v_nbuckets_940_ = lean_nat_mul(v___x_938_, v___x_939_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_box(0);
v___x_943_ = lean_mk_array(v_nbuckets_940_, v___x_942_);
v___x_944_ = lean_array_propagate_mark(v_data_937_, v___x_943_);
v___x_945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v___x_941_, v_data_937_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(lean_object* v_a_946_, lean_object* v_b_947_, lean_object* v_x_948_){
_start:
{
if (lean_obj_tag(v_x_948_) == 0)
{
lean_dec(v_b_947_);
lean_dec(v_a_946_);
return v_x_948_;
}
else
{
lean_object* v_key_949_; lean_object* v_value_950_; lean_object* v_tail_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_963_; 
v_key_949_ = lean_ctor_get(v_x_948_, 0);
v_value_950_ = lean_ctor_get(v_x_948_, 1);
v_tail_951_ = lean_ctor_get(v_x_948_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_948_);
if (v_isSharedCheck_963_ == 0)
{
v___x_953_ = v_x_948_;
v_isShared_954_ = v_isSharedCheck_963_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_tail_951_);
lean_inc(v_value_950_);
lean_inc(v_key_949_);
lean_dec(v_x_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_963_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_IR_instBEqJoinPointId_beq(v_key_949_, v_a_946_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_946_, v_b_947_, v_tail_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 2, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_key_949_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_value_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v___x_956_);
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
lean_dec(v_value_950_);
lean_dec(v_key_949_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_b_947_);
lean_ctor_set(v___x_953_, 0, v_a_946_);
v___x_961_ = v___x_953_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_946_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_b_947_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_tail_951_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_964_, lean_object* v_a_965_, lean_object* v_b_966_){
_start:
{
lean_object* v_size_967_; lean_object* v_buckets_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1011_; 
v_size_967_ = lean_ctor_get(v_m_964_, 0);
v_buckets_968_ = lean_ctor_get(v_m_964_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_m_964_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_970_ = v_m_964_;
v_isShared_971_ = v_isSharedCheck_1011_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_buckets_968_);
lean_inc(v_size_967_);
lean_dec(v_m_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1011_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; uint64_t v___x_975_; uint64_t v_fold_976_; uint64_t v___x_977_; uint64_t v___x_978_; uint64_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; lean_object* v_bkt_985_; uint8_t v___x_986_; 
v___x_972_ = lean_array_get_size(v_buckets_968_);
v___x_973_ = l_Lean_IR_instHashableJoinPointId_hash(v_a_965_);
v___x_974_ = 32ULL;
v___x_975_ = lean_uint64_shift_right(v___x_973_, v___x_974_);
v_fold_976_ = lean_uint64_xor(v___x_973_, v___x_975_);
v___x_977_ = 16ULL;
v___x_978_ = lean_uint64_shift_right(v_fold_976_, v___x_977_);
v___x_979_ = lean_uint64_xor(v_fold_976_, v___x_978_);
v___x_980_ = lean_uint64_to_usize(v___x_979_);
v___x_981_ = lean_usize_of_nat(v___x_972_);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_sub(v___x_981_, v___x_982_);
v___x_984_ = lean_usize_land(v___x_980_, v___x_983_);
v_bkt_985_ = lean_array_uget_borrowed(v_buckets_968_, v___x_984_);
v___x_986_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_965_, v_bkt_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v_size_x27_988_; lean_object* v___x_989_; lean_object* v_buckets_x27_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_987_ = lean_unsigned_to_nat(1u);
v_size_x27_988_ = lean_nat_add(v_size_967_, v___x_987_);
lean_dec(v_size_967_);
lean_inc(v_bkt_985_);
v___x_989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_989_, 0, v_a_965_);
lean_ctor_set(v___x_989_, 1, v_b_966_);
lean_ctor_set(v___x_989_, 2, v_bkt_985_);
v_buckets_x27_990_ = lean_array_uset(v_buckets_968_, v___x_984_, v___x_989_);
v___x_991_ = lean_unsigned_to_nat(4u);
v___x_992_ = lean_nat_mul(v_size_x27_988_, v___x_991_);
v___x_993_ = lean_unsigned_to_nat(3u);
v___x_994_ = lean_nat_div(v___x_992_, v___x_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_array_get_size(v_buckets_x27_990_);
v___x_996_ = lean_nat_dec_le(v___x_994_, v___x_995_);
lean_dec(v___x_994_);
if (v___x_996_ == 0)
{
lean_object* v_val_997_; lean_object* v___x_999_; 
v_val_997_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_buckets_x27_990_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v_val_997_);
lean_ctor_set(v___x_970_, 0, v_size_x27_988_);
v___x_999_ = v___x_970_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_size_x27_988_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_val_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
lean_object* v___x_1002_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v_buckets_x27_990_);
lean_ctor_set(v___x_970_, 0, v_size_x27_988_);
v___x_1002_ = v___x_970_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_size_x27_988_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_buckets_x27_990_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v___x_1004_; lean_object* v_buckets_x27_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_inc(v_bkt_985_);
v___x_1004_ = lean_box(0);
v_buckets_x27_1005_ = lean_array_uset(v_buckets_968_, v___x_984_, v___x_1004_);
v___x_1006_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_965_, v_b_966_, v_bkt_985_);
v___x_1007_ = lean_array_uset(v_buckets_x27_1005_, v___x_984_, v___x_1006_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1007_);
v___x_1009_ = v___x_970_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_size_967_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_1012_, lean_object* v_a_1013_){
_start:
{
switch(lean_obj_tag(v_x_1012_))
{
case 19:
{
lean_object* v_j_1014_; lean_object* v_xs_1015_; lean_object* v_v_1016_; lean_object* v_b_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_j_1014_ = lean_ctor_get(v_x_1012_, 0);
lean_inc(v_j_1014_);
v_xs_1015_ = lean_ctor_get(v_x_1012_, 1);
lean_inc_ref(v_xs_1015_);
v_v_1016_ = lean_ctor_get(v_x_1012_, 2);
lean_inc(v_v_1016_);
v_b_1017_ = lean_ctor_get(v_x_1012_, 3);
lean_inc(v_b_1017_);
lean_dec_ref_known(v_x_1012_, 4);
v___x_1018_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1017_, v_a_1013_);
v___x_1019_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_1016_, v___x_1018_);
v___x_1020_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1015_, v___x_1019_);
v_fst_1021_ = lean_ctor_get(v___x_1020_, 0);
v_snd_1022_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1020_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_inc(v_fst_1021_);
lean_dec(v___x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_1022_, v_j_1014_, v_xs_1015_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_fst_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
case 27:
{
lean_object* v_cs_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_cs_1031_ = lean_ctor_get(v_x_1012_, 3);
lean_inc_ref(v_cs_1031_);
lean_dec_ref_known(v_x_1012_, 4);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_array_get_size(v_cs_1031_);
v___x_1034_ = lean_nat_dec_lt(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v_cs_1031_);
return v_a_1013_;
}
else
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_nat_dec_le(v___x_1033_, v___x_1033_);
if (v___x_1035_ == 0)
{
if (v___x_1034_ == 0)
{
lean_dec_ref(v_cs_1031_);
return v_a_1013_;
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1033_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1031_, v___x_1036_, v___x_1037_, v_a_1013_);
lean_dec_ref(v_cs_1031_);
return v___x_1038_;
}
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1033_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_cs_1031_, v___x_1039_, v___x_1040_, v_a_1013_);
lean_dec_ref(v_cs_1031_);
return v___x_1041_;
}
}
}
default: 
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Lean_IR_FnBody_isVarDecl(v_x_1012_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_IR_FnBody_isTerminal(v_x_1012_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_IR_FnBody_body(v_x_1012_);
lean_dec(v_x_1012_);
v_x_1012_ = v___x_1044_;
goto _start;
}
else
{
lean_dec(v_x_1012_);
return v_a_1013_;
}
}
else
{
lean_object* v_b_1046_; lean_object* v___x_1047_; lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1059_; 
v_b_1046_ = l_Lean_IR_FnBody_body(v_x_1012_);
v___x_1047_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1046_, v_a_1013_);
v_fst_1048_ = lean_ctor_get(v___x_1047_, 0);
v_snd_1049_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1051_ = v___x_1047_;
v_isShared_1052_ = v_isSharedCheck_1059_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_inc(v_fst_1048_);
lean_dec(v___x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1059_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_x_1053_; lean_object* v_t_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v_x_1053_ = l_Lean_IR_FnBody_targetVar(v_x_1012_);
v_t_1054_ = l_Lean_IR_FnBody_targetType(v_x_1012_);
lean_dec(v_x_1012_);
v___x_1055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_1048_, v_x_1053_, v_t_1054_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1055_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_snd_1049_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_as_1060_, size_t v_i_1061_, size_t v_stop_1062_, lean_object* v_b_1063_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_eq(v_i_1061_, v_stop_1062_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; 
v___x_1065_ = lean_array_uget_borrowed(v_as_1060_, v_i_1061_);
v___x_1066_ = l_Lean_IR_Alt_body(v___x_1065_);
v___x_1067_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1066_, v_b_1063_);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1061_, v___x_1068_);
v_i_1061_ = v___x_1069_;
v_b_1063_ = v___x_1067_;
goto _start;
}
else
{
return v_b_1063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_as_1071_, lean_object* v_i_1072_, lean_object* v_stop_1073_, lean_object* v_b_1074_){
_start:
{
size_t v_i_boxed_1075_; size_t v_stop_boxed_1076_; lean_object* v_res_1077_; 
v_i_boxed_1075_ = lean_unbox_usize(v_i_1072_);
lean_dec(v_i_1072_);
v_stop_boxed_1076_ = lean_unbox_usize(v_stop_1073_);
lean_dec(v_stop_1073_);
v_res_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_as_1071_, v_i_boxed_1075_, v_stop_boxed_1076_, v_b_1074_);
lean_dec_ref(v_as_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1078_, lean_object* v_m_1079_, lean_object* v_a_1080_, lean_object* v_b_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1079_, v_a_1080_, v_b_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1083_, lean_object* v_a_1084_, lean_object* v_x_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_a_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_a_1088_, lean_object* v_x_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1087_, v_a_1088_, v_x_1089_);
lean_dec(v_x_1089_);
lean_dec(v_a_1088_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1(lean_object* v_00_u03b2_1092_, lean_object* v_data_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1___redArg(v_data_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2(lean_object* v_00_u03b2_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__2___redArg(v_a_1096_, v_b_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1100_, lean_object* v_i_1101_, lean_object* v_source_1102_, lean_object* v_target_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2___redArg(v_i_1101_, v_source_1102_, v_target_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1109_, lean_object* v_a_1110_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v_xs_1111_; lean_object* v_body_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_xs_1111_ = lean_ctor_get(v_x_1109_, 1);
lean_inc_ref(v_xs_1111_);
v_body_1112_ = lean_ctor_get(v_x_1109_, 3);
lean_inc(v_body_1112_);
lean_dec_ref_known(v_x_1109_, 5);
v___x_1113_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1112_, v_a_1110_);
v___x_1114_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1111_, v___x_1113_);
lean_dec_ref(v_xs_1111_);
return v___x_1114_;
}
else
{
lean_dec_ref(v_x_1109_);
return v_a_1110_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_unsigned_to_nat(16u);
v___x_1117_ = lean_mk_array(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1125_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1123_, v___x_1124_);
return v___x_1125_;
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
