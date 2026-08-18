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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_IR_Alt_body(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_IR_instHashableVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_IR_instBEqVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_IR_instHashableJoinPointId_hash(lean_object*);
uint8_t l_Lean_IR_instBEqJoinPointId_beq(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_instHashableJoinPointId_hash___boxed(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_IR_instBEqJoinPointId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_CollectMaps_collectJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instBEqJoinPointId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectMaps_collectJP___closed__0 = (const lean_object*)&l_Lean_IR_CollectMaps_collectJP___closed__0_value;
static const lean_closure_object l_Lean_IR_CollectMaps_collectJP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_instHashableJoinPointId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_CollectMaps_collectJP___closed__1 = (const lean_object*)&l_Lean_IR_CollectMaps_collectJP___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__0;
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__1;
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__2;
static lean_once_cell_t l_Lean_IR_mkVarJPMaps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_mkVarJPMaps___closed__3;
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
v___x_169_ = lean_nat_add(v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec(v___y_167_);
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
lean_ctor_set(v___x_149_, 3, v___y_166_);
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
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___y_166_);
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
v___y_166_ = v___x_181_;
v___y_167_ = v___x_182_;
v___y_168_ = v_size_183_;
goto v___jp_165_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(0u);
v___y_166_ = v___x_181_;
v___y_167_ = v___x_182_;
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
lean_dec_ref_known(v_x_424_, 4);
switch(lean_obj_tag(v_e_427_))
{
case 6:
{
lean_object* v_c_452_; 
v_c_452_ = lean_ctor_get(v_e_427_, 0);
lean_inc(v_c_452_);
lean_dec_ref_known(v_e_427_, 2);
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
lean_dec_ref_known(v_e_427_, 2);
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
v___x_436_ = lean_array_push(v___y_431_, v___y_430_);
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
lean_dec(v___y_430_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_snd_434_);
lean_ctor_set(v___x_439_, 1, v___y_431_);
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
v___y_430_ = v_f_442_;
v___y_431_ = v_order_446_;
v___y_432_ = v___y_443_;
v_fst_433_ = v___x_450_;
v_snd_434_ = v___x_449_;
goto v___jp_429_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_box(v___x_447_);
v___y_430_ = v_f_442_;
v___y_431_ = v_order_446_;
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
lean_dec_ref_known(v_x_424_, 4);
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
lean_dec_ref_known(v_x_424_, 4);
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
lean_dec_ref_known(v___x_526_, 1);
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
lean_dec_ref_known(v_x_558_, 5);
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
lean_dec_ref_known(v_x_558_, 4);
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
lean_dec_ref_known(v_as_572_, 2);
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
lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_718_; 
v_fst_637_ = lean_ctor_get(v_x_636_, 0);
v_snd_638_ = lean_ctor_get(v_x_636_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_718_ == 0)
{
v___x_640_ = v_x_636_;
v_isShared_641_ = v_isSharedCheck_718_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_inc(v_fst_637_);
lean_dec(v_x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_718_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___y_643_; lean_object* v_i_644_; lean_object* v___y_653_; lean_object* v_i_654_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___y_663_; lean_object* v___x_686_; 
v___x_660_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__0));
v___x_661_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectVar___closed__1));
lean_inc(v_x_634_);
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_660_, v___x_661_, v_fst_637_, v_x_634_);
switch(lean_obj_tag(v___x_686_))
{
case 0:
{
lean_object* v_index_687_; lean_object* v_size_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_del_object(v___x_640_);
v_index_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_index_687_);
lean_dec_ref_known(v___x_686_, 3);
v_size_688_ = lean_ctor_get(v_fst_637_, 0);
lean_inc(v_size_688_);
v___x_689_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_637_, v_size_688_, v_index_687_, v_x_634_, v_t_635_);
lean_dec(v_index_687_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_snd_638_);
return v___x_690_;
}
case 1:
{
lean_object* v_index_691_; lean_object* v_size_692_; lean_object* v_keyArray_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_index_691_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_index_691_);
lean_dec_ref_known(v___x_686_, 1);
v_size_692_ = lean_ctor_get(v_fst_637_, 0);
v_keyArray_693_ = lean_ctor_get(v_fst_637_, 1);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_size_692_, v___x_694_);
v___x_696_ = lean_array_get_size(v_keyArray_693_);
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec(v___x_695_);
lean_dec(v_index_691_);
goto v___jp_674_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_698_ = lean_unsigned_to_nat(4u);
v___x_699_ = lean_nat_mul(v___x_695_, v___x_698_);
v___x_700_ = lean_unsigned_to_nat(3u);
v___x_701_ = lean_nat_mul(v___x_696_, v___x_700_);
v___x_702_ = lean_nat_dec_le(v___x_699_, v___x_701_);
lean_dec(v___x_701_);
lean_dec(v___x_699_);
if (v___x_702_ == 0)
{
lean_dec(v___x_695_);
lean_dec(v_index_691_);
goto v___jp_674_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_del_object(v___x_640_);
v___x_703_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_637_, v___x_695_, v_index_691_, v_x_634_, v_t_635_);
lean_dec(v_index_691_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_snd_638_);
return v___x_704_;
}
}
}
default: 
{
lean_object* v_size_705_; lean_object* v_keyArray_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
lean_del_object(v___x_640_);
v_size_705_ = lean_ctor_get(v_fst_637_, 0);
v_keyArray_706_ = lean_ctor_get(v_fst_637_, 1);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_size_705_, v___x_707_);
v___x_709_ = lean_array_get_size(v_keyArray_706_);
v___x_710_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec(v___x_708_);
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_660_, v___x_661_, v_fst_637_);
v___y_663_ = v___x_711_;
goto v___jp_662_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_712_ = lean_unsigned_to_nat(4u);
v___x_713_ = lean_nat_mul(v___x_708_, v___x_712_);
lean_dec(v___x_708_);
v___x_714_ = lean_unsigned_to_nat(3u);
v___x_715_ = lean_nat_mul(v___x_709_, v___x_714_);
v___x_716_ = lean_nat_dec_le(v___x_713_, v___x_715_);
lean_dec(v___x_715_);
lean_dec(v___x_713_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_660_, v___x_661_, v_fst_637_);
v___y_663_ = v___x_717_;
goto v___jp_662_;
}
else
{
v___y_663_ = v_fst_637_;
goto v___jp_662_;
}
}
}
}
v___jp_642_:
{
lean_object* v_size_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v_size_645_ = lean_ctor_get(v___y_643_, 0);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_size_645_, v___x_646_);
v___x_648_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_643_, v___x_647_, v_i_644_, v_x_634_, v_t_635_);
lean_dec(v_i_644_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_648_);
v___x_650_ = v___x_640_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_638_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
v___jp_652_:
{
lean_object* v_size_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_size_655_ = lean_ctor_get(v___y_653_, 0);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_size_655_, v___x_656_);
v___x_658_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_653_, v___x_657_, v_i_654_, v_x_634_, v_t_635_);
lean_dec(v_i_654_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_snd_638_);
return v___x_659_;
}
v___jp_662_:
{
lean_object* v___x_664_; 
lean_inc(v_x_634_);
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_660_, v___x_661_, v___y_663_, v_x_634_);
switch(lean_obj_tag(v___x_664_))
{
case 0:
{
lean_object* v_index_665_; lean_object* v_size_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_index_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_index_665_);
lean_dec_ref_known(v___x_664_, 3);
v_size_666_ = lean_ctor_get(v___y_663_, 0);
lean_inc(v_size_666_);
v___x_667_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_663_, v_size_666_, v_index_665_, v_x_634_, v_t_635_);
lean_dec(v_index_665_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v_snd_638_);
return v___x_668_;
}
case 1:
{
lean_object* v_index_669_; 
v_index_669_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_index_669_);
lean_dec_ref_known(v___x_664_, 1);
v___y_653_ = v___y_663_;
v_i_654_ = v_index_669_;
goto v___jp_652_;
}
default: 
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_663_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_index_672_; 
v_index_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_index_672_);
lean_dec_ref_known(v___x_671_, 1);
v___y_653_ = v___y_663_;
v_i_654_ = v_index_672_;
goto v___jp_652_;
}
else
{
lean_object* v___x_673_; 
lean_dec(v_t_635_);
lean_dec(v_x_634_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___y_663_);
lean_ctor_set(v___x_673_, 1, v_snd_638_);
return v___x_673_;
}
}
}
}
v___jp_674_:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_660_, v___x_661_, v_fst_637_);
lean_inc(v_x_634_);
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_660_, v___x_661_, v___x_675_, v_x_634_);
switch(lean_obj_tag(v___x_676_))
{
case 0:
{
lean_object* v_index_677_; lean_object* v_size_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_del_object(v___x_640_);
v_index_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_index_677_);
lean_dec_ref_known(v___x_676_, 3);
v_size_678_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_size_678_);
v___x_679_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_675_, v_size_678_, v_index_677_, v_x_634_, v_t_635_);
lean_dec(v_index_677_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v_snd_638_);
return v___x_680_;
}
case 1:
{
lean_object* v_index_681_; 
v_index_681_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_index_681_);
lean_dec_ref_known(v___x_676_, 1);
v___y_643_ = v___x_675_;
v_i_644_ = v_index_681_;
goto v___jp_642_;
}
default: 
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_675_, v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_index_684_; 
v_index_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_index_684_);
lean_dec_ref_known(v___x_683_, 1);
v___y_643_ = v___x_675_;
v_i_644_ = v_index_684_;
goto v___jp_642_;
}
else
{
lean_object* v___x_685_; 
lean_del_object(v___x_640_);
lean_dec(v_t_635_);
lean_dec(v_x_634_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_675_);
lean_ctor_set(v___x_685_, 1, v_snd_638_);
return v___x_685_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(lean_object* v_m_719_, lean_object* v_query_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_zero_724_; uint8_t v_isZero_725_; 
v_zero_724_ = lean_unsigned_to_nat(0u);
v_isZero_725_ = lean_nat_dec_eq(v_x_722_, v_zero_724_);
if (v_isZero_725_ == 1)
{
lean_dec(v_x_723_);
lean_dec(v_x_722_);
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(2);
return v___x_726_;
}
else
{
lean_object* v_val_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_val_727_ = lean_ctor_get(v_x_721_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v_x_721_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_val_727_);
lean_dec(v_x_721_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_val_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_keyArray_735_; lean_object* v_valueArray_736_; lean_object* v___x_737_; uint8_t v_isSome_738_; 
v_keyArray_735_ = lean_ctor_get(v_m_719_, 1);
v_valueArray_736_ = lean_ctor_get(v_m_719_, 2);
v___x_737_ = lean_array_fget_borrowed(v_keyArray_735_, v_x_723_);
v_isSome_738_ = lean_noption_is_some(v___x_737_);
if (v_isSome_738_ == 0)
{
lean_dec(v_x_722_);
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_x_723_);
return v___x_739_;
}
else
{
lean_object* v_val_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_x_723_);
v_val_740_ = lean_ctor_get(v_x_721_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v_x_721_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_val_740_);
lean_dec(v_x_721_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_val_740_);
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
else
{
lean_object* v_one_748_; lean_object* v_n_749_; lean_object* v___y_751_; 
v_one_748_ = lean_unsigned_to_nat(1u);
v_n_749_ = lean_nat_sub(v_x_722_, v_one_748_);
lean_dec(v_x_722_);
if (v_isSome_738_ == 0)
{
goto v___jp_757_;
}
else
{
lean_object* v___x_759_; uint8_t v_isSome_760_; 
v___x_759_ = lean_array_fget_borrowed(v_valueArray_736_, v_x_723_);
v_isSome_760_ = lean_noption_is_some(v___x_759_);
if (v_isSome_760_ == 0)
{
goto v___jp_757_;
}
else
{
lean_object* v_val_761_; uint8_t v___x_762_; 
lean_inc(v___x_737_);
v_val_761_ = lean_noption_get(v___x_737_);
v___x_762_ = l_Lean_IR_instBEqVarId_beq(v_val_761_, v_query_720_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
lean_dec(v_val_761_);
v___x_763_ = lean_array_get_size(v_keyArray_735_);
v___x_764_ = lean_nat_add(v_x_723_, v_one_748_);
lean_dec(v_x_723_);
v___x_765_ = lean_nat_dec_lt(v___x_764_, v___x_763_);
if (v___x_765_ == 0)
{
lean_dec(v___x_764_);
v_x_722_ = v_n_749_;
v_x_723_ = v_zero_724_;
goto _start;
}
else
{
v_x_722_ = v_n_749_;
v_x_723_ = v___x_764_;
goto _start;
}
}
else
{
lean_object* v_val_768_; lean_object* v___x_769_; 
lean_dec(v_n_749_);
lean_dec(v_x_721_);
lean_inc(v___x_759_);
v_val_768_ = lean_noption_get(v___x_759_);
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v_x_723_);
lean_ctor_set(v___x_769_, 1, v_val_761_);
lean_ctor_set(v___x_769_, 2, v_val_768_);
return v___x_769_;
}
}
}
v___jp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_752_ = lean_array_get_size(v_keyArray_735_);
v___x_753_ = lean_nat_add(v_x_723_, v_one_748_);
lean_dec(v_x_723_);
v___x_754_ = lean_nat_dec_lt(v___x_753_, v___x_752_);
if (v___x_754_ == 0)
{
lean_dec(v___x_753_);
v_x_721_ = v___y_751_;
v_x_722_ = v_n_749_;
v_x_723_ = v_zero_724_;
goto _start;
}
else
{
v_x_721_ = v___y_751_;
v_x_722_ = v_n_749_;
v_x_723_ = v___x_753_;
goto _start;
}
}
v___jp_757_:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v___x_758_; 
lean_inc(v_x_723_);
v___x_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_758_, 0, v_x_723_);
v___y_751_ = v___x_758_;
goto v___jp_750_;
}
else
{
v___y_751_ = v_x_721_;
goto v___jp_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg___boxed(lean_object* v_m_770_, lean_object* v_query_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_m_770_, v_query_771_, v_x_772_, v_x_773_, v_x_774_);
lean_dec(v_query_771_);
lean_dec_ref(v_m_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(lean_object* v_m_776_, lean_object* v_query_777_){
_start:
{
lean_object* v_keyArray_778_; lean_object* v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v_fold_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_keyArray_778_ = lean_ctor_get(v_m_776_, 1);
v___x_779_ = lean_array_get_size(v_keyArray_778_);
v___x_780_ = l_Lean_IR_instHashableVarId_hash(v_query_777_);
v___x_781_ = 32ULL;
v___x_782_ = lean_uint64_shift_right(v___x_780_, v___x_781_);
v_fold_783_ = lean_uint64_xor(v___x_780_, v___x_782_);
v___x_784_ = 16ULL;
v___x_785_ = lean_uint64_shift_right(v_fold_783_, v___x_784_);
v___x_786_ = lean_uint64_xor(v_fold_783_, v___x_785_);
v___x_787_ = lean_uint64_to_usize(v___x_786_);
v___x_788_ = lean_usize_of_nat(v___x_779_);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_sub(v___x_788_, v___x_789_);
v___x_791_ = lean_usize_land(v___x_787_, v___x_790_);
v___x_792_ = lean_usize_to_nat(v___x_791_);
v___x_793_ = lean_box(0);
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_m_776_, v_query_777_, v___x_793_, v___x_779_, v___x_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg___boxed(lean_object* v_m_795_, lean_object* v_query_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_795_, v_query_796_);
lean_dec(v_query_796_);
lean_dec_ref(v_m_795_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg(lean_object* v_b_798_, lean_object* v_acc_799_, lean_object* v_i_800_){
_start:
{
lean_object* v___y_802_; lean_object* v_keyArray_810_; lean_object* v_valueArray_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_keyArray_810_ = lean_ctor_get(v_b_798_, 1);
v_valueArray_811_ = lean_ctor_get(v_b_798_, 2);
v___x_812_ = lean_array_get_size(v_keyArray_810_);
v___x_813_ = lean_nat_dec_lt(v_i_800_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_i_800_);
return v_acc_799_;
}
else
{
lean_object* v___x_814_; uint8_t v_isSome_815_; 
v___x_814_ = lean_array_fget_borrowed(v_keyArray_810_, v_i_800_);
v_isSome_815_ = lean_noption_is_some(v___x_814_);
if (v_isSome_815_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v___x_816_; uint8_t v_isSome_817_; 
v___x_816_ = lean_array_fget_borrowed(v_valueArray_811_, v_i_800_);
v_isSome_817_ = lean_noption_is_some(v___x_816_);
if (v_isSome_817_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v_val_818_; lean_object* v_val_819_; lean_object* v_i_821_; lean_object* v___x_826_; 
lean_inc(v___x_814_);
v_val_818_ = lean_noption_get(v___x_814_);
lean_inc(v___x_816_);
v_val_819_ = lean_noption_get(v___x_816_);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_acc_799_, v_val_818_);
switch(lean_obj_tag(v___x_826_))
{
case 0:
{
lean_object* v_index_827_; lean_object* v_size_828_; lean_object* v___x_829_; 
v_index_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_827_);
lean_dec_ref_known(v___x_826_, 3);
v_size_828_ = lean_ctor_get(v_acc_799_, 0);
lean_inc(v_size_828_);
v___x_829_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_799_, v_size_828_, v_index_827_, v_val_818_, v_val_819_);
lean_dec(v_index_827_);
v___y_802_ = v___x_829_;
goto v___jp_801_;
}
case 1:
{
lean_object* v_index_830_; 
v_index_830_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_index_830_);
lean_dec_ref_known(v___x_826_, 1);
v_i_821_ = v_index_830_;
goto v___jp_820_;
}
default: 
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_799_, v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_index_833_; 
v_index_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_index_833_);
lean_dec_ref_known(v___x_832_, 1);
v_i_821_ = v_index_833_;
goto v___jp_820_;
}
else
{
lean_dec(v_val_819_);
lean_dec(v_val_818_);
v___y_802_ = v_acc_799_;
goto v___jp_801_;
}
}
}
v___jp_820_:
{
lean_object* v_size_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_size_822_ = lean_ctor_get(v_acc_799_, 0);
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_size_822_, v___x_823_);
v___x_825_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_799_, v___x_824_, v_i_821_, v_val_818_, v_val_819_);
lean_dec(v_i_821_);
v___y_802_ = v___x_825_;
goto v___jp_801_;
}
}
}
}
v___jp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_i_800_, v___x_803_);
lean_dec(v_i_800_);
v_acc_799_ = v___y_802_;
v_i_800_ = v___x_804_;
goto _start;
}
v___jp_806_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_i_800_, v___x_807_);
lean_dec(v_i_800_);
v_i_800_ = v___x_808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_834_, lean_object* v_acc_835_, lean_object* v_i_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg(v_b_834_, v_acc_835_, v_i_836_);
lean_dec_ref(v_b_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg(lean_object* v_init_838_, lean_object* v_b_839_){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg(v_b_839_, v_init_838_, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg___boxed(lean_object* v_init_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg(v_init_842_, v_b_843_);
lean_dec_ref(v_b_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(lean_object* v_m_845_){
_start:
{
lean_object* v_keyArray_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_cellCount_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_target_853_; lean_object* v___x_854_; 
v_keyArray_846_ = lean_ctor_get(v_m_845_, 1);
v___x_847_ = lean_array_get_size(v_keyArray_846_);
v___x_848_ = lean_unsigned_to_nat(2u);
v_cellCount_849_ = lean_nat_mul(v___x_847_, v___x_848_);
v___x_850_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_849_);
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_849_);
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_849_);
v_target_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_853_, 0, v___x_850_);
lean_ctor_set(v_target_853_, 1, v___x_851_);
lean_ctor_set(v_target_853_, 2, v___x_852_);
v___x_854_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg(v_target_853_, v_m_845_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg___boxed(lean_object* v_m_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_m_855_);
lean_dec_ref(v_m_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2(lean_object* v_as_857_, size_t v_i_858_, size_t v_stop_859_, lean_object* v_b_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_eq(v_i_858_, v_stop_859_);
if (v___x_861_ == 0)
{
lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_942_; 
v_fst_862_ = lean_ctor_get(v_b_860_, 0);
v_snd_863_ = lean_ctor_get(v_b_860_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_b_860_);
if (v_isSharedCheck_942_ == 0)
{
v___x_865_ = v_b_860_;
v_isShared_866_ = v_isSharedCheck_942_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snd_863_);
lean_inc(v_fst_862_);
lean_dec(v_b_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_942_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___y_868_; lean_object* v___x_875_; lean_object* v_x_876_; lean_object* v_ty_877_; lean_object* v___y_879_; lean_object* v_i_880_; lean_object* v___y_886_; lean_object* v___y_896_; lean_object* v_i_897_; lean_object* v___x_912_; 
v___x_875_ = lean_array_uget_borrowed(v_as_857_, v_i_858_);
v_x_876_ = lean_ctor_get(v___x_875_, 0);
v_ty_877_ = lean_ctor_get(v___x_875_, 1);
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_862_, v_x_876_);
switch(lean_obj_tag(v___x_912_))
{
case 0:
{
lean_object* v_index_913_; lean_object* v_size_914_; lean_object* v___x_915_; 
v_index_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_index_913_);
lean_dec_ref_known(v___x_912_, 3);
v_size_914_ = lean_ctor_get(v_fst_862_, 0);
lean_inc(v_size_914_);
lean_inc(v_ty_877_);
lean_inc(v_x_876_);
v___x_915_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_862_, v_size_914_, v_index_913_, v_x_876_, v_ty_877_);
lean_dec(v_index_913_);
v___y_868_ = v___x_915_;
goto v___jp_867_;
}
case 1:
{
lean_object* v_index_916_; lean_object* v_size_917_; lean_object* v_keyArray_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_index_916_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_index_916_);
lean_dec_ref_known(v___x_912_, 1);
v_size_917_ = lean_ctor_get(v_fst_862_, 0);
v_keyArray_918_ = lean_ctor_get(v_fst_862_, 1);
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_add(v_size_917_, v___x_919_);
v___x_921_ = lean_array_get_size(v_keyArray_918_);
v___x_922_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
if (v___x_922_ == 0)
{
lean_dec(v___x_920_);
lean_dec(v_index_916_);
goto v___jp_902_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_923_ = lean_unsigned_to_nat(4u);
v___x_924_ = lean_nat_mul(v___x_920_, v___x_923_);
v___x_925_ = lean_unsigned_to_nat(3u);
v___x_926_ = lean_nat_mul(v___x_921_, v___x_925_);
v___x_927_ = lean_nat_dec_le(v___x_924_, v___x_926_);
lean_dec(v___x_926_);
lean_dec(v___x_924_);
if (v___x_927_ == 0)
{
lean_dec(v___x_920_);
lean_dec(v_index_916_);
goto v___jp_902_;
}
else
{
lean_object* v___x_928_; 
lean_inc(v_ty_877_);
lean_inc(v_x_876_);
v___x_928_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_862_, v___x_920_, v_index_916_, v_x_876_, v_ty_877_);
lean_dec(v_index_916_);
v___y_868_ = v___x_928_;
goto v___jp_867_;
}
}
}
default: 
{
lean_object* v_size_929_; lean_object* v_keyArray_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_size_929_ = lean_ctor_get(v_fst_862_, 0);
v_keyArray_930_ = lean_ctor_get(v_fst_862_, 1);
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_add(v_size_929_, v___x_931_);
v___x_933_ = lean_array_get_size(v_keyArray_930_);
v___x_934_ = lean_nat_dec_lt(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v___x_932_);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_fst_862_);
lean_dec(v_fst_862_);
v___y_886_ = v___x_935_;
goto v___jp_885_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_936_ = lean_unsigned_to_nat(4u);
v___x_937_ = lean_nat_mul(v___x_932_, v___x_936_);
lean_dec(v___x_932_);
v___x_938_ = lean_unsigned_to_nat(3u);
v___x_939_ = lean_nat_mul(v___x_933_, v___x_938_);
v___x_940_ = lean_nat_dec_le(v___x_937_, v___x_939_);
lean_dec(v___x_939_);
lean_dec(v___x_937_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_fst_862_);
lean_dec(v_fst_862_);
v___y_886_ = v___x_941_;
goto v___jp_885_;
}
else
{
v___y_886_ = v_fst_862_;
goto v___jp_885_;
}
}
}
}
v___jp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___y_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___y_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_snd_863_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
size_t v___x_871_; size_t v___x_872_; 
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_add(v_i_858_, v___x_871_);
v_i_858_ = v___x_872_;
v_b_860_ = v___x_870_;
goto _start;
}
}
v___jp_878_:
{
lean_object* v_size_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_size_881_ = lean_ctor_get(v___y_879_, 0);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_size_881_, v___x_882_);
lean_inc(v_ty_877_);
lean_inc(v_x_876_);
v___x_884_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_879_, v___x_883_, v_i_880_, v_x_876_, v_ty_877_);
lean_dec(v_i_880_);
v___y_868_ = v___x_884_;
goto v___jp_867_;
}
v___jp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v___y_886_, v_x_876_);
switch(lean_obj_tag(v___x_887_))
{
case 0:
{
lean_object* v_index_888_; lean_object* v_size_889_; lean_object* v___x_890_; 
v_index_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_index_888_);
lean_dec_ref_known(v___x_887_, 3);
v_size_889_ = lean_ctor_get(v___y_886_, 0);
lean_inc(v_size_889_);
lean_inc(v_ty_877_);
lean_inc(v_x_876_);
v___x_890_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_886_, v_size_889_, v_index_888_, v_x_876_, v_ty_877_);
lean_dec(v_index_888_);
v___y_868_ = v___x_890_;
goto v___jp_867_;
}
case 1:
{
lean_object* v_index_891_; 
v_index_891_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_index_891_);
lean_dec_ref_known(v___x_887_, 1);
v___y_879_ = v___y_886_;
v_i_880_ = v_index_891_;
goto v___jp_878_;
}
default: 
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_886_, v___x_892_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_index_894_; 
v_index_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_index_894_);
lean_dec_ref_known(v___x_893_, 1);
v___y_879_ = v___y_886_;
v_i_880_ = v_index_894_;
goto v___jp_878_;
}
else
{
v___y_868_ = v___y_886_;
goto v___jp_867_;
}
}
}
}
v___jp_895_:
{
lean_object* v_size_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_size_898_ = lean_ctor_get(v___y_896_, 0);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_add(v_size_898_, v___x_899_);
lean_inc(v_ty_877_);
lean_inc(v_x_876_);
v___x_901_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_896_, v___x_900_, v_i_897_, v_x_876_, v_ty_877_);
lean_dec(v_i_897_);
v___y_868_ = v___x_901_;
goto v___jp_867_;
}
v___jp_902_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_fst_862_);
lean_dec(v_fst_862_);
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v___x_903_, v_x_876_);
switch(lean_obj_tag(v___x_904_))
{
case 0:
{
lean_object* v_index_905_; lean_object* v_size_906_; lean_object* v___x_907_; 
v_index_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_index_905_);
lean_dec_ref_known(v___x_904_, 3);
v_size_906_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_size_906_);
lean_inc(v_ty_877_);
lean_inc(v_x_876_);
v___x_907_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_903_, v_size_906_, v_index_905_, v_x_876_, v_ty_877_);
lean_dec(v_index_905_);
v___y_868_ = v___x_907_;
goto v___jp_867_;
}
case 1:
{
lean_object* v_index_908_; 
v_index_908_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_index_908_);
lean_dec_ref_known(v___x_904_, 1);
v___y_896_ = v___x_903_;
v_i_897_ = v_index_908_;
goto v___jp_895_;
}
default: 
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_903_, v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_index_911_; 
v_index_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_index_911_);
lean_dec_ref_known(v___x_910_, 1);
v___y_896_ = v___x_903_;
v_i_897_ = v_index_911_;
goto v___jp_895_;
}
else
{
v___y_868_ = v___x_903_;
goto v___jp_867_;
}
}
}
}
}
}
else
{
return v_b_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2___boxed(lean_object* v_as_943_, lean_object* v_i_944_, lean_object* v_stop_945_, lean_object* v_b_946_){
_start:
{
size_t v_i_boxed_947_; size_t v_stop_boxed_948_; lean_object* v_res_949_; 
v_i_boxed_947_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_stop_boxed_948_ = lean_unbox_usize(v_stop_945_);
lean_dec(v_stop_945_);
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2(v_as_943_, v_i_boxed_947_, v_stop_boxed_948_, v_b_946_);
lean_dec_ref(v_as_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams(lean_object* v_ps_950_, lean_object* v_s_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_array_get_size(v_ps_950_);
v___x_954_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
if (v___x_954_ == 0)
{
return v_s_951_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = lean_nat_dec_le(v___x_953_, v___x_953_);
if (v___x_955_ == 0)
{
if (v___x_954_ == 0)
{
return v_s_951_;
}
else
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_953_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2(v_ps_950_, v___x_956_, v___x_957_, v_s_951_);
return v___x_958_;
}
}
else
{
size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((size_t)0ULL);
v___x_960_ = lean_usize_of_nat(v___x_953_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectParams_spec__2(v_ps_950_, v___x_959_, v___x_960_, v_s_951_);
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectParams___boxed(lean_object* v_ps_962_, lean_object* v_s_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_IR_CollectMaps_collectParams(v_ps_962_, v_s_963_);
lean_dec_ref(v_ps_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0(lean_object* v_00_u03b2_965_, lean_object* v_m_966_, lean_object* v_query_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_m_966_, v_query_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___boxed(lean_object* v_00_u03b2_969_, lean_object* v_m_970_, lean_object* v_query_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0(v_00_u03b2_969_, v_m_970_, v_query_971_);
lean_dec(v_query_971_);
lean_dec_ref(v_m_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1(lean_object* v_00_u03b2_973_, lean_object* v_m_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_m_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___boxed(lean_object* v_00_u03b2_976_, lean_object* v_m_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1(v_00_u03b2_976_, v_m_977_);
lean_dec_ref(v_m_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(lean_object* v_00_u03b2_979_, lean_object* v_m_980_, lean_object* v_query_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___redArg(v_m_980_, v_query_981_, v_x_982_, v_x_983_, v_x_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0___boxed(lean_object* v_00_u03b2_987_, lean_object* v_m_988_, lean_object* v_query_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0_spec__0(v_00_u03b2_987_, v_m_988_, v_query_989_, v_x_990_, v_x_991_, v_x_992_, v_x_993_);
lean_dec(v_query_989_);
lean_dec_ref(v_m_988_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2(lean_object* v_00_u03b2_995_, lean_object* v_init_996_, lean_object* v_b_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___redArg(v_init_996_, v_b_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2___boxed(lean_object* v_00_u03b2_999_, lean_object* v_init_1000_, lean_object* v_b_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2(v_00_u03b2_999_, v_init_1000_, v_b_1001_);
lean_dec_ref(v_b_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1003_, lean_object* v_b_1004_, lean_object* v_acc_1005_, lean_object* v_i_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___redArg(v_b_1004_, v_acc_1005_, v_i_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1008_, lean_object* v_b_1009_, lean_object* v_acc_1010_, lean_object* v_i_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1_spec__2_spec__3(v_00_u03b2_1008_, v_b_1009_, v_acc_1010_, v_i_1011_);
lean_dec_ref(v_b_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectJP(lean_object* v_j_1015_, lean_object* v_xs_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1099_; 
v_fst_1018_ = lean_ctor_get(v_x_1017_, 0);
v_snd_1019_ = lean_ctor_get(v_x_1017_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1017_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1021_ = v_x_1017_;
v_isShared_1022_ = v_isSharedCheck_1099_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_snd_1019_);
lean_inc(v_fst_1018_);
lean_dec(v_x_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1099_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___y_1024_; lean_object* v_i_1025_; lean_object* v___y_1034_; lean_object* v_i_1035_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___y_1044_; lean_object* v___x_1067_; 
v___x_1041_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__0));
v___x_1042_ = ((lean_object*)(l_Lean_IR_CollectMaps_collectJP___closed__1));
lean_inc(v_j_1015_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1041_, v___x_1042_, v_snd_1019_, v_j_1015_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_del_object(v___x_1021_);
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v_snd_1019_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1019_, v_size_1069_, v_index_1068_, v_j_1015_, v_xs_1016_);
lean_dec(v_index_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_fst_1018_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
return v___x_1071_;
}
case 1:
{
lean_object* v_index_1072_; lean_object* v_size_1073_; lean_object* v_keyArray_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_index_1072_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1072_);
lean_dec_ref_known(v___x_1067_, 1);
v_size_1073_ = lean_ctor_get(v_snd_1019_, 0);
v_keyArray_1074_ = lean_ctor_get(v_snd_1019_, 1);
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = lean_nat_add(v_size_1073_, v___x_1075_);
v___x_1077_ = lean_array_get_size(v_keyArray_1074_);
v___x_1078_ = lean_nat_dec_lt(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec(v___x_1076_);
lean_dec(v_index_1072_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1079_ = lean_unsigned_to_nat(4u);
v___x_1080_ = lean_nat_mul(v___x_1076_, v___x_1079_);
v___x_1081_ = lean_unsigned_to_nat(3u);
v___x_1082_ = lean_nat_mul(v___x_1077_, v___x_1081_);
v___x_1083_ = lean_nat_dec_le(v___x_1080_, v___x_1082_);
lean_dec(v___x_1082_);
lean_dec(v___x_1080_);
if (v___x_1083_ == 0)
{
lean_dec(v___x_1076_);
lean_dec(v_index_1072_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_del_object(v___x_1021_);
v___x_1084_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1019_, v___x_1076_, v_index_1072_, v_j_1015_, v_xs_1016_);
lean_dec(v_index_1072_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_fst_1018_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
return v___x_1085_;
}
}
}
default: 
{
lean_object* v_size_1086_; lean_object* v_keyArray_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
lean_del_object(v___x_1021_);
v_size_1086_ = lean_ctor_get(v_snd_1019_, 0);
v_keyArray_1087_ = lean_ctor_get(v_snd_1019_, 1);
v___x_1088_ = lean_unsigned_to_nat(1u);
v___x_1089_ = lean_nat_add(v_size_1086_, v___x_1088_);
v___x_1090_ = lean_array_get_size(v_keyArray_1087_);
v___x_1091_ = lean_nat_dec_lt(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_dec(v___x_1089_);
v___x_1092_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1041_, v___x_1042_, v_snd_1019_);
v___y_1044_ = v___x_1092_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1093_ = lean_unsigned_to_nat(4u);
v___x_1094_ = lean_nat_mul(v___x_1089_, v___x_1093_);
lean_dec(v___x_1089_);
v___x_1095_ = lean_unsigned_to_nat(3u);
v___x_1096_ = lean_nat_mul(v___x_1090_, v___x_1095_);
v___x_1097_ = lean_nat_dec_le(v___x_1094_, v___x_1096_);
lean_dec(v___x_1096_);
lean_dec(v___x_1094_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1041_, v___x_1042_, v_snd_1019_);
v___y_1044_ = v___x_1098_;
goto v___jp_1043_;
}
else
{
v___y_1044_ = v_snd_1019_;
goto v___jp_1043_;
}
}
}
}
v___jp_1023_:
{
lean_object* v_size_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v_size_1026_ = lean_ctor_get(v___y_1024_, 0);
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_size_1026_, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1024_, v___x_1028_, v_i_1025_, v_j_1015_, v_xs_1016_);
lean_dec(v_i_1025_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___x_1029_);
v___x_1031_ = v___x_1021_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_fst_1018_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
v___jp_1033_:
{
lean_object* v_size_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_size_1036_ = lean_ctor_get(v___y_1034_, 0);
v___x_1037_ = lean_unsigned_to_nat(1u);
v___x_1038_ = lean_nat_add(v_size_1036_, v___x_1037_);
v___x_1039_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1034_, v___x_1038_, v_i_1035_, v_j_1015_, v_xs_1016_);
lean_dec(v_i_1035_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_fst_1018_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
return v___x_1040_;
}
v___jp_1043_:
{
lean_object* v___x_1045_; 
lean_inc(v_j_1015_);
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1041_, v___x_1042_, v___y_1044_, v_j_1015_);
switch(lean_obj_tag(v___x_1045_))
{
case 0:
{
lean_object* v_index_1046_; lean_object* v_size_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_index_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_index_1046_);
lean_dec_ref_known(v___x_1045_, 3);
v_size_1047_ = lean_ctor_get(v___y_1044_, 0);
lean_inc(v_size_1047_);
v___x_1048_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1044_, v_size_1047_, v_index_1046_, v_j_1015_, v_xs_1016_);
lean_dec(v_index_1046_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_fst_1018_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
return v___x_1049_;
}
case 1:
{
lean_object* v_index_1050_; 
v_index_1050_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_index_1050_);
lean_dec_ref_known(v___x_1045_, 1);
v___y_1034_ = v___y_1044_;
v_i_1035_ = v_index_1050_;
goto v___jp_1033_;
}
default: 
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1044_, v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_index_1053_; 
v_index_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_index_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v___y_1034_ = v___y_1044_;
v_i_1035_ = v_index_1053_;
goto v___jp_1033_;
}
else
{
lean_object* v___x_1054_; 
lean_dec_ref(v_xs_1016_);
lean_dec(v_j_1015_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_fst_1018_);
lean_ctor_set(v___x_1054_, 1, v___y_1044_);
return v___x_1054_;
}
}
}
}
v___jp_1055_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_1041_, v___x_1042_, v_snd_1019_);
lean_inc(v_j_1015_);
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_1041_, v___x_1042_, v___x_1056_, v_j_1015_);
switch(lean_obj_tag(v___x_1057_))
{
case 0:
{
lean_object* v_index_1058_; lean_object* v_size_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_del_object(v___x_1021_);
v_index_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_index_1058_);
lean_dec_ref_known(v___x_1057_, 3);
v_size_1059_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_size_1059_);
v___x_1060_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1056_, v_size_1059_, v_index_1058_, v_j_1015_, v_xs_1016_);
lean_dec(v_index_1058_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v_fst_1018_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
return v___x_1061_;
}
case 1:
{
lean_object* v_index_1062_; 
v_index_1062_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_index_1062_);
lean_dec_ref_known(v___x_1057_, 1);
v___y_1024_ = v___x_1056_;
v_i_1025_ = v_index_1062_;
goto v___jp_1023_;
}
default: 
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1056_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_index_1065_; 
v_index_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_index_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___y_1024_ = v___x_1056_;
v_i_1025_ = v_index_1065_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1066_; 
lean_del_object(v___x_1021_);
lean_dec_ref(v_xs_1016_);
lean_dec(v_j_1015_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_fst_1018_);
lean_ctor_set(v___x_1066_, 1, v___x_1056_);
return v___x_1066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(lean_object* v_m_1100_, lean_object* v_query_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_zero_1105_; uint8_t v_isZero_1106_; 
v_zero_1105_ = lean_unsigned_to_nat(0u);
v_isZero_1106_ = lean_nat_dec_eq(v_x_1103_, v_zero_1105_);
if (v_isZero_1106_ == 1)
{
lean_dec(v_x_1104_);
lean_dec(v_x_1103_);
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_box(2);
return v___x_1107_;
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_val_1108_ = lean_ctor_get(v_x_1102_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v_x_1102_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_val_1108_);
lean_dec(v_x_1102_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_val_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_keyArray_1116_; lean_object* v_valueArray_1117_; lean_object* v___x_1118_; uint8_t v_isSome_1119_; 
v_keyArray_1116_ = lean_ctor_get(v_m_1100_, 1);
v_valueArray_1117_ = lean_ctor_get(v_m_1100_, 2);
v___x_1118_ = lean_array_fget_borrowed(v_keyArray_1116_, v_x_1104_);
v_isSome_1119_ = lean_noption_is_some(v___x_1118_);
if (v_isSome_1119_ == 0)
{
lean_dec(v_x_1103_);
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_x_1104_);
return v___x_1120_;
}
else
{
lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_x_1104_);
v_val_1121_ = lean_ctor_get(v_x_1102_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v_x_1102_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_dec(v_x_1102_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_val_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_one_1129_; lean_object* v_n_1130_; lean_object* v___y_1132_; 
v_one_1129_ = lean_unsigned_to_nat(1u);
v_n_1130_ = lean_nat_sub(v_x_1103_, v_one_1129_);
lean_dec(v_x_1103_);
if (v_isSome_1119_ == 0)
{
goto v___jp_1138_;
}
else
{
lean_object* v___x_1140_; uint8_t v_isSome_1141_; 
v___x_1140_ = lean_array_fget_borrowed(v_valueArray_1117_, v_x_1104_);
v_isSome_1141_ = lean_noption_is_some(v___x_1140_);
if (v_isSome_1141_ == 0)
{
goto v___jp_1138_;
}
else
{
lean_object* v_val_1142_; uint8_t v___x_1143_; 
lean_inc(v___x_1118_);
v_val_1142_ = lean_noption_get(v___x_1118_);
v___x_1143_ = l_Lean_IR_instBEqJoinPointId_beq(v_val_1142_, v_query_1101_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
lean_dec(v_val_1142_);
v___x_1144_ = lean_array_get_size(v_keyArray_1116_);
v___x_1145_ = lean_nat_add(v_x_1104_, v_one_1129_);
lean_dec(v_x_1104_);
v___x_1146_ = lean_nat_dec_lt(v___x_1145_, v___x_1144_);
if (v___x_1146_ == 0)
{
lean_dec(v___x_1145_);
v_x_1103_ = v_n_1130_;
v_x_1104_ = v_zero_1105_;
goto _start;
}
else
{
v_x_1103_ = v_n_1130_;
v_x_1104_ = v___x_1145_;
goto _start;
}
}
else
{
lean_object* v_val_1149_; lean_object* v___x_1150_; 
lean_dec(v_n_1130_);
lean_dec(v_x_1102_);
lean_inc(v___x_1140_);
v_val_1149_ = lean_noption_get(v___x_1140_);
v___x_1150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1150_, 0, v_x_1104_);
lean_ctor_set(v___x_1150_, 1, v_val_1142_);
lean_ctor_set(v___x_1150_, 2, v_val_1149_);
return v___x_1150_;
}
}
}
v___jp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = lean_array_get_size(v_keyArray_1116_);
v___x_1134_ = lean_nat_add(v_x_1104_, v_one_1129_);
lean_dec(v_x_1104_);
v___x_1135_ = lean_nat_dec_lt(v___x_1134_, v___x_1133_);
if (v___x_1135_ == 0)
{
lean_dec(v___x_1134_);
v_x_1102_ = v___y_1132_;
v_x_1103_ = v_n_1130_;
v_x_1104_ = v_zero_1105_;
goto _start;
}
else
{
v_x_1102_ = v___y_1132_;
v_x_1103_ = v_n_1130_;
v_x_1104_ = v___x_1134_;
goto _start;
}
}
v___jp_1138_:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v___x_1139_; 
lean_inc(v_x_1104_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_x_1104_);
v___y_1132_ = v___x_1139_;
goto v___jp_1131_;
}
else
{
v___y_1132_ = v_x_1102_;
goto v___jp_1131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg___boxed(lean_object* v_m_1151_, lean_object* v_query_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_m_1151_, v_query_1152_, v_x_1153_, v_x_1154_, v_x_1155_);
lean_dec(v_query_1152_);
lean_dec_ref(v_m_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(lean_object* v_m_1157_, lean_object* v_query_1158_){
_start:
{
lean_object* v_keyArray_1159_; lean_object* v___x_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; uint64_t v_fold_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_keyArray_1159_ = lean_ctor_get(v_m_1157_, 1);
v___x_1160_ = lean_array_get_size(v_keyArray_1159_);
v___x_1161_ = l_Lean_IR_instHashableJoinPointId_hash(v_query_1158_);
v___x_1162_ = 32ULL;
v___x_1163_ = lean_uint64_shift_right(v___x_1161_, v___x_1162_);
v_fold_1164_ = lean_uint64_xor(v___x_1161_, v___x_1163_);
v___x_1165_ = 16ULL;
v___x_1166_ = lean_uint64_shift_right(v_fold_1164_, v___x_1165_);
v___x_1167_ = lean_uint64_xor(v_fold_1164_, v___x_1166_);
v___x_1168_ = lean_uint64_to_usize(v___x_1167_);
v___x_1169_ = lean_usize_of_nat(v___x_1160_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_sub(v___x_1169_, v___x_1170_);
v___x_1172_ = lean_usize_land(v___x_1168_, v___x_1171_);
v___x_1173_ = lean_usize_to_nat(v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_m_1157_, v_query_1158_, v___x_1174_, v___x_1160_, v___x_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg___boxed(lean_object* v_m_1176_, lean_object* v_query_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1176_, v_query_1177_);
lean_dec(v_query_1177_);
lean_dec_ref(v_m_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg(lean_object* v_b_1179_, lean_object* v_acc_1180_, lean_object* v_i_1181_){
_start:
{
lean_object* v___y_1183_; lean_object* v_keyArray_1191_; lean_object* v_valueArray_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v_keyArray_1191_ = lean_ctor_get(v_b_1179_, 1);
v_valueArray_1192_ = lean_ctor_get(v_b_1179_, 2);
v___x_1193_ = lean_array_get_size(v_keyArray_1191_);
v___x_1194_ = lean_nat_dec_lt(v_i_1181_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_dec(v_i_1181_);
return v_acc_1180_;
}
else
{
lean_object* v___x_1195_; uint8_t v_isSome_1196_; 
v___x_1195_ = lean_array_fget_borrowed(v_keyArray_1191_, v_i_1181_);
v_isSome_1196_ = lean_noption_is_some(v___x_1195_);
if (v_isSome_1196_ == 0)
{
goto v___jp_1187_;
}
else
{
lean_object* v___x_1197_; uint8_t v_isSome_1198_; 
v___x_1197_ = lean_array_fget_borrowed(v_valueArray_1192_, v_i_1181_);
v_isSome_1198_ = lean_noption_is_some(v___x_1197_);
if (v_isSome_1198_ == 0)
{
goto v___jp_1187_;
}
else
{
lean_object* v_val_1199_; lean_object* v_val_1200_; lean_object* v_i_1202_; lean_object* v___x_1207_; 
lean_inc(v___x_1195_);
v_val_1199_ = lean_noption_get(v___x_1195_);
lean_inc(v___x_1197_);
v_val_1200_ = lean_noption_get(v___x_1197_);
v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_acc_1180_, v_val_1199_);
switch(lean_obj_tag(v___x_1207_))
{
case 0:
{
lean_object* v_index_1208_; lean_object* v_size_1209_; lean_object* v___x_1210_; 
v_index_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_index_1208_);
lean_dec_ref_known(v___x_1207_, 3);
v_size_1209_ = lean_ctor_get(v_acc_1180_, 0);
lean_inc(v_size_1209_);
v___x_1210_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1180_, v_size_1209_, v_index_1208_, v_val_1199_, v_val_1200_);
lean_dec(v_index_1208_);
v___y_1183_ = v___x_1210_;
goto v___jp_1182_;
}
case 1:
{
lean_object* v_index_1211_; 
v_index_1211_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_index_1211_);
lean_dec_ref_known(v___x_1207_, 1);
v_i_1202_ = v_index_1211_;
goto v___jp_1201_;
}
default: 
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1180_, v___x_1212_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_index_1214_; 
v_index_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_index_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_i_1202_ = v_index_1214_;
goto v___jp_1201_;
}
else
{
lean_dec(v_val_1200_);
lean_dec(v_val_1199_);
v___y_1183_ = v_acc_1180_;
goto v___jp_1182_;
}
}
}
v___jp_1201_:
{
lean_object* v_size_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_size_1203_ = lean_ctor_get(v_acc_1180_, 0);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_nat_add(v_size_1203_, v___x_1204_);
v___x_1206_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1180_, v___x_1205_, v_i_1202_, v_val_1199_, v_val_1200_);
lean_dec(v_i_1202_);
v___y_1183_ = v___x_1206_;
goto v___jp_1182_;
}
}
}
}
v___jp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = lean_nat_add(v_i_1181_, v___x_1184_);
lean_dec(v_i_1181_);
v_acc_1180_ = v___y_1183_;
v_i_1181_ = v___x_1185_;
goto _start;
}
v___jp_1187_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_i_1181_, v___x_1188_);
lean_dec(v_i_1181_);
v_i_1181_ = v___x_1189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_1215_, lean_object* v_acc_1216_, lean_object* v_i_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg(v_b_1215_, v_acc_1216_, v_i_1217_);
lean_dec_ref(v_b_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg(lean_object* v_init_1219_, lean_object* v_b_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg(v_b_1220_, v_init_1219_, v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg___boxed(lean_object* v_init_1223_, lean_object* v_b_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg(v_init_1223_, v_b_1224_);
lean_dec_ref(v_b_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(lean_object* v_m_1226_){
_start:
{
lean_object* v_keyArray_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_cellCount_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_target_1234_; lean_object* v___x_1235_; 
v_keyArray_1227_ = lean_ctor_get(v_m_1226_, 1);
v___x_1228_ = lean_array_get_size(v_keyArray_1227_);
v___x_1229_ = lean_unsigned_to_nat(2u);
v_cellCount_1230_ = lean_nat_mul(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1230_);
v___x_1232_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1230_);
v___x_1233_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1230_);
v_target_1234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1234_, 0, v___x_1231_);
lean_ctor_set(v_target_1234_, 1, v___x_1232_);
lean_ctor_set(v_target_1234_, 2, v___x_1233_);
v___x_1235_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg(v_target_1234_, v_m_1226_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg___boxed(lean_object* v_m_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(v_m_1236_);
lean_dec_ref(v_m_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectFnBody(lean_object* v_x_1238_, lean_object* v_a_1239_){
_start:
{
switch(lean_obj_tag(v_x_1238_))
{
case 0:
{
lean_object* v_x_1240_; lean_object* v_ty_1241_; lean_object* v_b_1242_; lean_object* v___x_1243_; lean_object* v_fst_1244_; lean_object* v_snd_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1323_; 
v_x_1240_ = lean_ctor_get(v_x_1238_, 0);
lean_inc(v_x_1240_);
v_ty_1241_ = lean_ctor_get(v_x_1238_, 1);
lean_inc(v_ty_1241_);
v_b_1242_ = lean_ctor_get(v_x_1238_, 3);
lean_inc(v_b_1242_);
lean_dec_ref_known(v_x_1238_, 4);
v___x_1243_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1242_, v_a_1239_);
v_fst_1244_ = lean_ctor_get(v___x_1243_, 0);
v_snd_1245_ = lean_ctor_get(v___x_1243_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1247_ = v___x_1243_;
v_isShared_1248_ = v_isSharedCheck_1323_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1244_);
lean_dec(v___x_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1323_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___y_1250_; lean_object* v_i_1251_; lean_object* v___y_1260_; lean_object* v_i_1261_; lean_object* v___y_1268_; lean_object* v___x_1291_; 
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v_fst_1244_, v_x_1240_);
switch(lean_obj_tag(v___x_1291_))
{
case 0:
{
lean_object* v_index_1292_; lean_object* v_size_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_del_object(v___x_1247_);
v_index_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_index_1292_);
lean_dec_ref_known(v___x_1291_, 3);
v_size_1293_ = lean_ctor_get(v_fst_1244_, 0);
lean_inc(v_size_1293_);
v___x_1294_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1244_, v_size_1293_, v_index_1292_, v_x_1240_, v_ty_1241_);
lean_dec(v_index_1292_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v_snd_1245_);
return v___x_1295_;
}
case 1:
{
lean_object* v_index_1296_; lean_object* v_size_1297_; lean_object* v_keyArray_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_index_1296_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_index_1296_);
lean_dec_ref_known(v___x_1291_, 1);
v_size_1297_ = lean_ctor_get(v_fst_1244_, 0);
v_keyArray_1298_ = lean_ctor_get(v_fst_1244_, 1);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_size_1297_, v___x_1299_);
v___x_1301_ = lean_array_get_size(v_keyArray_1298_);
v___x_1302_ = lean_nat_dec_lt(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec(v___x_1300_);
lean_dec(v_index_1296_);
goto v___jp_1279_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1303_ = lean_unsigned_to_nat(4u);
v___x_1304_ = lean_nat_mul(v___x_1300_, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(3u);
v___x_1306_ = lean_nat_mul(v___x_1301_, v___x_1305_);
v___x_1307_ = lean_nat_dec_le(v___x_1304_, v___x_1306_);
lean_dec(v___x_1306_);
lean_dec(v___x_1304_);
if (v___x_1307_ == 0)
{
lean_dec(v___x_1300_);
lean_dec(v_index_1296_);
goto v___jp_1279_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_del_object(v___x_1247_);
v___x_1308_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1244_, v___x_1300_, v_index_1296_, v_x_1240_, v_ty_1241_);
lean_dec(v_index_1296_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_snd_1245_);
return v___x_1309_;
}
}
}
default: 
{
lean_object* v_size_1310_; lean_object* v_keyArray_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
lean_del_object(v___x_1247_);
v_size_1310_ = lean_ctor_get(v_fst_1244_, 0);
v_keyArray_1311_ = lean_ctor_get(v_fst_1244_, 1);
v___x_1312_ = lean_unsigned_to_nat(1u);
v___x_1313_ = lean_nat_add(v_size_1310_, v___x_1312_);
v___x_1314_ = lean_array_get_size(v_keyArray_1311_);
v___x_1315_ = lean_nat_dec_lt(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec(v___x_1313_);
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_fst_1244_);
lean_dec(v_fst_1244_);
v___y_1268_ = v___x_1316_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1317_ = lean_unsigned_to_nat(4u);
v___x_1318_ = lean_nat_mul(v___x_1313_, v___x_1317_);
lean_dec(v___x_1313_);
v___x_1319_ = lean_unsigned_to_nat(3u);
v___x_1320_ = lean_nat_mul(v___x_1314_, v___x_1319_);
v___x_1321_ = lean_nat_dec_le(v___x_1318_, v___x_1320_);
lean_dec(v___x_1320_);
lean_dec(v___x_1318_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_fst_1244_);
lean_dec(v_fst_1244_);
v___y_1268_ = v___x_1322_;
goto v___jp_1267_;
}
else
{
v___y_1268_ = v_fst_1244_;
goto v___jp_1267_;
}
}
}
}
v___jp_1249_:
{
lean_object* v_size_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v_size_1252_ = lean_ctor_get(v___y_1250_, 0);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_add(v_size_1252_, v___x_1253_);
v___x_1255_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1250_, v___x_1254_, v_i_1251_, v_x_1240_, v_ty_1241_);
lean_dec(v_i_1251_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1255_);
v___x_1257_ = v___x_1247_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_snd_1245_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
v___jp_1259_:
{
lean_object* v_size_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_size_1262_ = lean_ctor_get(v___y_1260_, 0);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_add(v_size_1262_, v___x_1263_);
v___x_1265_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1260_, v___x_1264_, v_i_1261_, v_x_1240_, v_ty_1241_);
lean_dec(v_i_1261_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_snd_1245_);
return v___x_1266_;
}
v___jp_1267_:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v___y_1268_, v_x_1240_);
switch(lean_obj_tag(v___x_1269_))
{
case 0:
{
lean_object* v_index_1270_; lean_object* v_size_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_index_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_index_1270_);
lean_dec_ref_known(v___x_1269_, 3);
v_size_1271_ = lean_ctor_get(v___y_1268_, 0);
lean_inc(v_size_1271_);
v___x_1272_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1268_, v_size_1271_, v_index_1270_, v_x_1240_, v_ty_1241_);
lean_dec(v_index_1270_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v_snd_1245_);
return v___x_1273_;
}
case 1:
{
lean_object* v_index_1274_; 
v_index_1274_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_index_1274_);
lean_dec_ref_known(v___x_1269_, 1);
v___y_1260_ = v___y_1268_;
v_i_1261_ = v_index_1274_;
goto v___jp_1259_;
}
default: 
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1268_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_index_1277_; 
v_index_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_index_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___y_1260_ = v___y_1268_;
v_i_1261_ = v_index_1277_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1278_; 
lean_dec(v_ty_1241_);
lean_dec(v_x_1240_);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___y_1268_);
lean_ctor_set(v___x_1278_, 1, v_snd_1245_);
return v___x_1278_;
}
}
}
}
v___jp_1279_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectParams_spec__1___redArg(v_fst_1244_);
lean_dec(v_fst_1244_);
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectParams_spec__0___redArg(v___x_1280_, v_x_1240_);
switch(lean_obj_tag(v___x_1281_))
{
case 0:
{
lean_object* v_index_1282_; lean_object* v_size_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_del_object(v___x_1247_);
v_index_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_index_1282_);
lean_dec_ref_known(v___x_1281_, 3);
v_size_1283_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_size_1283_);
v___x_1284_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1280_, v_size_1283_, v_index_1282_, v_x_1240_, v_ty_1241_);
lean_dec(v_index_1282_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_snd_1245_);
return v___x_1285_;
}
case 1:
{
lean_object* v_index_1286_; 
v_index_1286_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_index_1286_);
lean_dec_ref_known(v___x_1281_, 1);
v___y_1250_ = v___x_1280_;
v_i_1251_ = v_index_1286_;
goto v___jp_1249_;
}
default: 
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1280_, v___x_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_index_1289_; 
v_index_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_index_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v___y_1250_ = v___x_1280_;
v_i_1251_ = v_index_1289_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1290_; 
lean_del_object(v___x_1247_);
lean_dec(v_ty_1241_);
lean_dec(v_x_1240_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1280_);
lean_ctor_set(v___x_1290_, 1, v_snd_1245_);
return v___x_1290_;
}
}
}
}
}
}
case 1:
{
lean_object* v_j_1324_; lean_object* v_xs_1325_; lean_object* v_v_1326_; lean_object* v_b_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1410_; 
v_j_1324_ = lean_ctor_get(v_x_1238_, 0);
lean_inc(v_j_1324_);
v_xs_1325_ = lean_ctor_get(v_x_1238_, 1);
lean_inc_ref(v_xs_1325_);
v_v_1326_ = lean_ctor_get(v_x_1238_, 2);
lean_inc(v_v_1326_);
v_b_1327_ = lean_ctor_get(v_x_1238_, 3);
lean_inc(v_b_1327_);
lean_dec_ref_known(v_x_1238_, 4);
v___x_1328_ = l_Lean_IR_CollectMaps_collectFnBody(v_b_1327_, v_a_1239_);
v___x_1329_ = l_Lean_IR_CollectMaps_collectFnBody(v_v_1326_, v___x_1328_);
v___x_1330_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1325_, v___x_1329_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1334_ = v___x_1330_;
v_isShared_1335_ = v_isSharedCheck_1410_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snd_1332_);
lean_inc(v_fst_1331_);
lean_dec(v___x_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1410_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___y_1337_; lean_object* v_i_1338_; lean_object* v___y_1347_; lean_object* v___y_1359_; lean_object* v_i_1360_; lean_object* v___x_1378_; 
v___x_1378_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_snd_1332_, v_j_1324_);
switch(lean_obj_tag(v___x_1378_))
{
case 0:
{
lean_object* v_index_1379_; lean_object* v_size_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1334_);
v_index_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_index_1379_);
lean_dec_ref_known(v___x_1378_, 3);
v_size_1380_ = lean_ctor_get(v_snd_1332_, 0);
lean_inc(v_size_1380_);
v___x_1381_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1332_, v_size_1380_, v_index_1379_, v_j_1324_, v_xs_1325_);
lean_dec(v_index_1379_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_fst_1331_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
return v___x_1382_;
}
case 1:
{
lean_object* v_index_1383_; lean_object* v_size_1384_; lean_object* v_keyArray_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
lean_del_object(v___x_1334_);
v_index_1383_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_index_1383_);
lean_dec_ref_known(v___x_1378_, 1);
v_size_1384_ = lean_ctor_get(v_snd_1332_, 0);
v_keyArray_1385_ = lean_ctor_get(v_snd_1332_, 1);
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v_size_1384_, v___x_1386_);
v___x_1388_ = lean_array_get_size(v_keyArray_1385_);
v___x_1389_ = lean_nat_dec_lt(v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_dec(v___x_1387_);
lean_dec(v_index_1383_);
goto v___jp_1366_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1390_ = lean_unsigned_to_nat(4u);
v___x_1391_ = lean_nat_mul(v___x_1387_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(3u);
v___x_1393_ = lean_nat_mul(v___x_1388_, v___x_1392_);
v___x_1394_ = lean_nat_dec_le(v___x_1391_, v___x_1393_);
lean_dec(v___x_1393_);
lean_dec(v___x_1391_);
if (v___x_1394_ == 0)
{
lean_dec(v___x_1387_);
lean_dec(v_index_1383_);
goto v___jp_1366_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1332_, v___x_1387_, v_index_1383_, v_j_1324_, v_xs_1325_);
lean_dec(v_index_1383_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_fst_1331_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
return v___x_1396_;
}
}
}
default: 
{
lean_object* v_size_1397_; lean_object* v_keyArray_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1397_ = lean_ctor_get(v_snd_1332_, 0);
v_keyArray_1398_ = lean_ctor_get(v_snd_1332_, 1);
v___x_1399_ = lean_unsigned_to_nat(1u);
v___x_1400_ = lean_nat_add(v_size_1397_, v___x_1399_);
v___x_1401_ = lean_array_get_size(v_keyArray_1398_);
v___x_1402_ = lean_nat_dec_lt(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
lean_dec(v___x_1400_);
v___x_1403_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(v_snd_1332_);
lean_dec(v_snd_1332_);
v___y_1347_ = v___x_1403_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1404_ = lean_unsigned_to_nat(4u);
v___x_1405_ = lean_nat_mul(v___x_1400_, v___x_1404_);
lean_dec(v___x_1400_);
v___x_1406_ = lean_unsigned_to_nat(3u);
v___x_1407_ = lean_nat_mul(v___x_1401_, v___x_1406_);
v___x_1408_ = lean_nat_dec_le(v___x_1405_, v___x_1407_);
lean_dec(v___x_1407_);
lean_dec(v___x_1405_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(v_snd_1332_);
lean_dec(v_snd_1332_);
v___y_1347_ = v___x_1409_;
goto v___jp_1346_;
}
else
{
v___y_1347_ = v_snd_1332_;
goto v___jp_1346_;
}
}
}
}
v___jp_1336_:
{
lean_object* v_size_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v_size_1339_ = lean_ctor_get(v___y_1337_, 0);
v___x_1340_ = lean_unsigned_to_nat(1u);
v___x_1341_ = lean_nat_add(v_size_1339_, v___x_1340_);
v___x_1342_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1337_, v___x_1341_, v_i_1338_, v_j_1324_, v_xs_1325_);
lean_dec(v_i_1338_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1342_);
v___x_1344_ = v___x_1334_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_fst_1331_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
v___jp_1346_:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v___y_1347_, v_j_1324_);
switch(lean_obj_tag(v___x_1348_))
{
case 0:
{
lean_object* v_index_1349_; lean_object* v_size_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_del_object(v___x_1334_);
v_index_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_index_1349_);
lean_dec_ref_known(v___x_1348_, 3);
v_size_1350_ = lean_ctor_get(v___y_1347_, 0);
lean_inc(v_size_1350_);
v___x_1351_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1347_, v_size_1350_, v_index_1349_, v_j_1324_, v_xs_1325_);
lean_dec(v_index_1349_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_fst_1331_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
return v___x_1352_;
}
case 1:
{
lean_object* v_index_1353_; 
v_index_1353_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_index_1353_);
lean_dec_ref_known(v___x_1348_, 1);
v___y_1337_ = v___y_1347_;
v_i_1338_ = v_index_1353_;
goto v___jp_1336_;
}
default: 
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1347_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_index_1356_; 
v_index_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_index_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___y_1337_ = v___y_1347_;
v_i_1338_ = v_index_1356_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1357_; 
lean_del_object(v___x_1334_);
lean_dec_ref(v_xs_1325_);
lean_dec(v_j_1324_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_fst_1331_);
lean_ctor_set(v___x_1357_, 1, v___y_1347_);
return v___x_1357_;
}
}
}
}
v___jp_1358_:
{
lean_object* v_size_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_size_1361_ = lean_ctor_get(v___y_1359_, 0);
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_add(v_size_1361_, v___x_1362_);
v___x_1364_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1359_, v___x_1363_, v_i_1360_, v_j_1324_, v_xs_1325_);
lean_dec(v_i_1360_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_fst_1331_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
return v___x_1365_;
}
v___jp_1366_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(v_snd_1332_);
lean_dec(v_snd_1332_);
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v___x_1367_, v_j_1324_);
switch(lean_obj_tag(v___x_1368_))
{
case 0:
{
lean_object* v_index_1369_; lean_object* v_size_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_index_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_index_1369_);
lean_dec_ref_known(v___x_1368_, 3);
v_size_1370_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_size_1370_);
v___x_1371_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1367_, v_size_1370_, v_index_1369_, v_j_1324_, v_xs_1325_);
lean_dec(v_index_1369_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_fst_1331_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
return v___x_1372_;
}
case 1:
{
lean_object* v_index_1373_; 
v_index_1373_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_index_1373_);
lean_dec_ref_known(v___x_1368_, 1);
v___y_1359_ = v___x_1367_;
v_i_1360_ = v_index_1373_;
goto v___jp_1358_;
}
default: 
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1367_, v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_index_1376_; 
v_index_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_index_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___y_1359_ = v___x_1367_;
v_i_1360_ = v_index_1376_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1377_; 
lean_dec_ref(v_xs_1325_);
lean_dec(v_j_1324_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_fst_1331_);
lean_ctor_set(v___x_1377_, 1, v___x_1367_);
return v___x_1377_;
}
}
}
}
}
}
case 9:
{
lean_object* v_cs_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_cs_1411_ = lean_ctor_get(v_x_1238_, 3);
lean_inc_ref(v_cs_1411_);
lean_dec_ref_known(v_x_1238_, 4);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_cs_1411_);
v___x_1414_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_dec_ref(v_cs_1411_);
return v_a_1239_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_le(v___x_1413_, v___x_1413_);
if (v___x_1415_ == 0)
{
if (v___x_1414_ == 0)
{
lean_dec_ref(v_cs_1411_);
return v_a_1239_;
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1413_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2(v_cs_1411_, v___x_1416_, v___x_1417_, v_a_1239_);
lean_dec_ref(v_cs_1411_);
return v___x_1418_;
}
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1413_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2(v_cs_1411_, v___x_1419_, v___x_1420_, v_a_1239_);
lean_dec_ref(v_cs_1411_);
return v___x_1421_;
}
}
}
default: 
{
uint8_t v___x_1422_; 
v___x_1422_ = l_Lean_IR_FnBody_isTerminal(v_x_1238_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_IR_FnBody_body(v_x_1238_);
lean_dec(v_x_1238_);
v_x_1238_ = v___x_1423_;
goto _start;
}
else
{
lean_dec(v_x_1238_);
return v_a_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2(lean_object* v_as_1425_, size_t v_i_1426_, size_t v_stop_1427_, lean_object* v_b_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_usize_dec_eq(v_i_1426_, v_stop_1427_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v___x_1433_; size_t v___x_1434_; 
v___x_1430_ = lean_array_uget_borrowed(v_as_1425_, v_i_1426_);
v___x_1431_ = l_Lean_IR_Alt_body(v___x_1430_);
v___x_1432_ = l_Lean_IR_CollectMaps_collectFnBody(v___x_1431_, v_b_1428_);
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1426_, v___x_1433_);
v_i_1426_ = v___x_1434_;
v_b_1428_ = v___x_1432_;
goto _start;
}
else
{
return v_b_1428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2___boxed(lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_stop_1438_, lean_object* v_b_1439_){
_start:
{
size_t v_i_boxed_1440_; size_t v_stop_boxed_1441_; lean_object* v_res_1442_; 
v_i_boxed_1440_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_stop_boxed_1441_ = lean_unbox_usize(v_stop_1438_);
lean_dec(v_stop_1438_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_CollectMaps_collectFnBody_spec__2(v_as_1436_, v_i_boxed_1440_, v_stop_boxed_1441_, v_b_1439_);
lean_dec_ref(v_as_1436_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(lean_object* v_00_u03b2_1443_, lean_object* v_m_1444_, lean_object* v_query_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___redArg(v_m_1444_, v_query_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_m_1448_, lean_object* v_query_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0(v_00_u03b2_1447_, v_m_1448_, v_query_1449_);
lean_dec(v_query_1449_);
lean_dec_ref(v_m_1448_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___redArg(v_m_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1___boxed(lean_object* v_00_u03b2_1454_, lean_object* v_m_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1(v_00_u03b2_1454_, v_m_1455_);
lean_dec_ref(v_m_1455_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(lean_object* v_00_u03b2_1457_, lean_object* v_m_1458_, lean_object* v_query_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___redArg(v_m_1458_, v_query_1459_, v_x_1460_, v_x_1461_, v_x_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_m_1466_, lean_object* v_query_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_IR_CollectMaps_collectFnBody_spec__0_spec__0(v_00_u03b2_1465_, v_m_1466_, v_query_1467_, v_x_1468_, v_x_1469_, v_x_1470_, v_x_1471_);
lean_dec(v_query_1467_);
lean_dec_ref(v_m_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2(lean_object* v_00_u03b2_1473_, lean_object* v_init_1474_, lean_object* v_b_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___redArg(v_init_1474_, v_b_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_init_1478_, lean_object* v_b_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2(v_00_u03b2_1477_, v_init_1478_, v_b_1479_);
lean_dec_ref(v_b_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1481_, lean_object* v_b_1482_, lean_object* v_acc_1483_, lean_object* v_i_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___redArg(v_b_1482_, v_acc_1483_, v_i_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1486_, lean_object* v_b_1487_, lean_object* v_acc_1488_, lean_object* v_i_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_IR_CollectMaps_collectFnBody_spec__1_spec__2_spec__3(v_00_u03b2_1486_, v_b_1487_, v_acc_1488_, v_i_1489_);
lean_dec_ref(v_b_1487_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CollectMaps_collectDecl(lean_object* v_x_1491_, lean_object* v_a_1492_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_xs_1493_; lean_object* v_body_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_xs_1493_ = lean_ctor_get(v_x_1491_, 1);
lean_inc_ref(v_xs_1493_);
v_body_1494_ = lean_ctor_get(v_x_1491_, 3);
lean_inc(v_body_1494_);
lean_dec_ref_known(v_x_1491_, 5);
v___x_1495_ = l_Lean_IR_CollectMaps_collectFnBody(v_body_1494_, v_a_1492_);
v___x_1496_ = l_Lean_IR_CollectMaps_collectParams(v_xs_1493_, v___x_1495_);
lean_dec_ref(v_xs_1493_);
return v___x_1496_;
}
else
{
lean_dec_ref(v_x_1491_);
return v_a_1492_;
}
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__0(void){
_start:
{
lean_object* v_cellCount_1497_; lean_object* v___x_1498_; 
v_cellCount_1497_ = lean_unsigned_to_nat(16u);
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__1(void){
_start:
{
lean_object* v_cellCount_1499_; lean_object* v___x_1500_; 
v_cellCount_1499_ = lean_unsigned_to_nat(16u);
v___x_1500_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__2(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__1, &l_Lean_IR_mkVarJPMaps___closed__1_once, _init_l_Lean_IR_mkVarJPMaps___closed__1);
v___x_1502_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__0, &l_Lean_IR_mkVarJPMaps___closed__0_once, _init_l_Lean_IR_mkVarJPMaps___closed__0);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v___x_1501_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_IR_mkVarJPMaps___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__2, &l_Lean_IR_mkVarJPMaps___closed__2_once, _init_l_Lean_IR_mkVarJPMaps___closed__2);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkVarJPMaps(lean_object* v_d_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_obj_once(&l_Lean_IR_mkVarJPMaps___closed__3, &l_Lean_IR_mkVarJPMaps___closed__3_once, _init_l_Lean_IR_mkVarJPMaps___closed__3);
v___x_1509_ = l_Lean_IR_CollectMaps_collectDecl(v_d_1507_, v___x_1508_);
return v___x_1509_;
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
