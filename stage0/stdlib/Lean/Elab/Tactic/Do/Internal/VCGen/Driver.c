// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Driver
// Imports: public import Lean.Elab.Tactic.Meta public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Solve public import Lean.Meta.Sym.Grind
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renameI"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value),LEAN_SCALAR_PTR_LITERAL(20, 41, 101, 89, 107, 117, 242, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rename_i"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__27_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(lean_object* v_mvarId_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_mctx_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_mctx_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_mctx_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_5_, v_mvarId_1_);
lean_dec_ref(v_mctx_5_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object* v_mvarId_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mvarId_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec(v_mvarId_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(lean_object* v_mvarId_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mvarId_12_, v___y_16_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___boxed(lean_object* v_mvarId_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(v_mvarId_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v_mvarId_21_);
return v_res_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0(lean_object* v_x_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0___boxed(lean_object* v_x_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0(v_x_32_);
lean_dec(v_x_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_keys_35_, lean_object* v_i_36_, lean_object* v_k_37_){
_start:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_array_get_size(v_keys_35_);
v___x_39_ = lean_nat_dec_lt(v_i_36_, v___x_38_);
if (v___x_39_ == 0)
{
lean_dec(v_i_36_);
return v___x_39_;
}
else
{
lean_object* v_k_x27_40_; uint8_t v___x_41_; 
v_k_x27_40_ = lean_array_fget_borrowed(v_keys_35_, v_i_36_);
v___x_41_ = l_Lean_instBEqMVarId_beq(v_k_37_, v_k_x27_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_i_36_, v___x_42_);
lean_dec(v_i_36_);
v_i_36_ = v___x_43_;
goto _start;
}
else
{
lean_dec(v_i_36_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_keys_45_, lean_object* v_i_46_, lean_object* v_k_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_45_, v_i_46_, v_k_47_);
lean_dec(v_k_47_);
lean_dec_ref(v_keys_45_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_50_, size_t v_x_51_, lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_es_53_; lean_object* v___x_54_; size_t v___x_55_; size_t v___x_56_; lean_object* v_j_57_; lean_object* v___x_58_; 
v_es_53_ = lean_ctor_get(v_x_50_, 0);
v___x_54_ = lean_box(2);
v___x_55_ = ((size_t)31ULL);
v___x_56_ = lean_usize_land(v_x_51_, v___x_55_);
v_j_57_ = lean_usize_to_nat(v___x_56_);
v___x_58_ = lean_array_get_borrowed(v___x_54_, v_es_53_, v_j_57_);
lean_dec(v_j_57_);
switch(lean_obj_tag(v___x_58_))
{
case 0:
{
lean_object* v_key_59_; uint8_t v___x_60_; 
v_key_59_ = lean_ctor_get(v___x_58_, 0);
v___x_60_ = l_Lean_instBEqMVarId_beq(v_x_52_, v_key_59_);
return v___x_60_;
}
case 1:
{
lean_object* v_node_61_; size_t v___x_62_; size_t v___x_63_; 
v_node_61_ = lean_ctor_get(v___x_58_, 0);
v___x_62_ = ((size_t)5ULL);
v___x_63_ = lean_usize_shift_right(v_x_51_, v___x_62_);
v_x_50_ = v_node_61_;
v_x_51_ = v___x_63_;
goto _start;
}
default: 
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
else
{
lean_object* v_ks_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_ks_66_ = lean_ctor_get(v_x_50_, 0);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_66_, v___x_67_, v_x_52_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_69_, lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
size_t v_x_17579__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_17579__boxed_72_ = lean_unbox_usize(v_x_70_);
lean_dec(v_x_70_);
v_res_73_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_69_, v_x_17579__boxed_72_, v_x_71_);
lean_dec(v_x_71_);
lean_dec_ref(v_x_69_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint64_t v___x_77_; size_t v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Lean_instHashableMVarId_hash(v_x_76_);
v___x_78_ = lean_uint64_to_usize(v___x_77_);
v___x_79_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_75_, v___x_78_, v_x_76_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_80_, v_x_81_);
lean_dec(v_x_81_);
lean_dec_ref(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v_mctx_88_; lean_object* v_eAssignment_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_87_ = lean_st_ref_get(v___y_85_);
v_mctx_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_mctx_88_);
lean_dec(v___x_87_);
v_eAssignment_89_ = lean_ctor_get(v_mctx_88_, 8);
lean_inc_ref(v_eAssignment_89_);
lean_dec_ref(v_mctx_88_);
v___x_90_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_89_, v_mvarId_84_);
lean_dec_ref(v_eAssignment_89_);
v___x_91_ = lean_box(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec(v_mvarId_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_ks_101_; lean_object* v_vs_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_126_; 
v_ks_101_ = lean_ctor_get(v_x_97_, 0);
v_vs_102_ = lean_ctor_get(v_x_97_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_97_);
if (v_isSharedCheck_126_ == 0)
{
v___x_104_ = v_x_97_;
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_vs_102_);
lean_inc(v_ks_101_);
lean_dec(v_x_97_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_array_get_size(v_ks_101_);
v___x_107_ = lean_nat_dec_lt(v_x_98_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec(v_x_98_);
v___x_108_ = lean_array_push(v_ks_101_, v_x_99_);
v___x_109_ = lean_array_push(v_vs_102_, v_x_100_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_109_);
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_111_ = v___x_104_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
else
{
lean_object* v_k_x27_113_; uint8_t v___x_114_; 
v_k_x27_113_ = lean_array_fget_borrowed(v_ks_101_, v_x_98_);
v___x_114_ = l_Lean_instBEqMVarId_beq(v_x_99_, v_k_x27_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_116_; 
if (v_isShared_105_ == 0)
{
v___x_116_ = v___x_104_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_ks_101_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_vs_102_);
v___x_116_ = v_reuseFailAlloc_120_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_x_98_, v___x_117_);
lean_dec(v_x_98_);
v_x_97_ = v___x_116_;
v_x_98_ = v___x_118_;
goto _start;
}
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_121_ = lean_array_fset(v_ks_101_, v_x_98_, v_x_99_);
v___x_122_ = lean_array_fset(v_vs_102_, v_x_98_, v_x_100_);
lean_dec(v_x_98_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_122_);
lean_ctor_set(v___x_104_, 0, v___x_121_);
v___x_124_ = v___x_104_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_n_127_, lean_object* v_k_128_, lean_object* v_v_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_n_127_, v___x_130_, v_k_128_, v_v_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object* v_x_133_, size_t v_x_134_, size_t v_x_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v_es_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v_j_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_es_138_ = lean_ctor_get(v_x_133_, 0);
v___x_139_ = ((size_t)31ULL);
v___x_140_ = lean_usize_land(v_x_134_, v___x_139_);
v_j_141_ = lean_usize_to_nat(v___x_140_);
v___x_142_ = lean_array_get_size(v_es_138_);
v___x_143_ = lean_nat_dec_lt(v_j_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_j_141_);
lean_dec(v_x_137_);
lean_dec(v_x_136_);
return v_x_133_;
}
else
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_182_; 
lean_inc_ref(v_es_138_);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_x_133_, 0);
lean_dec(v_unused_183_);
v___x_145_ = v_x_133_;
v_isShared_146_ = v_isSharedCheck_182_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_182_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_v_147_; lean_object* v___x_148_; lean_object* v_xs_x27_149_; lean_object* v___y_151_; 
v_v_147_ = lean_array_fget(v_es_138_, v_j_141_);
v___x_148_ = lean_box(0);
v_xs_x27_149_ = lean_array_fset(v_es_138_, v_j_141_, v___x_148_);
switch(lean_obj_tag(v_v_147_))
{
case 0:
{
lean_object* v_key_156_; lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_167_; 
v_key_156_ = lean_ctor_get(v_v_147_, 0);
v_val_157_ = lean_ctor_get(v_v_147_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_v_147_);
if (v_isSharedCheck_167_ == 0)
{
v___x_159_ = v_v_147_;
v_isShared_160_ = v_isSharedCheck_167_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_inc(v_key_156_);
lean_dec(v_v_147_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_167_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_instBEqMVarId_beq(v_x_136_, v_key_156_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_del_object(v___x_159_);
v___x_162_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_156_, v_val_157_, v_x_136_, v_x_137_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___y_151_ = v___x_163_;
goto v___jp_150_;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_val_157_);
lean_dec(v_key_156_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_x_137_);
lean_ctor_set(v___x_159_, 0, v_x_136_);
v___x_165_ = v___x_159_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_x_136_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_x_137_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v___y_151_ = v___x_165_;
goto v___jp_150_;
}
}
}
}
case 1:
{
lean_object* v_node_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_180_; 
v_node_168_ = lean_ctor_get(v_v_147_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_v_147_);
if (v_isSharedCheck_180_ == 0)
{
v___x_170_ = v_v_147_;
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_node_168_);
lean_dec(v_v_147_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_usize_shift_right(v_x_134_, v___x_172_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_x_135_, v___x_174_);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_node_168_, v___x_173_, v___x_175_, v_x_136_, v_x_137_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_176_);
v___x_178_ = v___x_170_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v___y_151_ = v___x_178_;
goto v___jp_150_;
}
}
}
default: 
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_x_136_);
lean_ctor_set(v___x_181_, 1, v_x_137_);
v___y_151_ = v___x_181_;
goto v___jp_150_;
}
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_array_fset(v_xs_x27_149_, v_j_141_, v___y_151_);
lean_dec(v_j_141_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_152_);
v___x_154_ = v___x_145_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
else
{
lean_object* v_ks_184_; lean_object* v_vs_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_205_; 
v_ks_184_ = lean_ctor_get(v_x_133_, 0);
v_vs_185_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_205_ == 0)
{
v___x_187_ = v_x_133_;
v_isShared_188_ = v_isSharedCheck_205_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_vs_185_);
lean_inc(v_ks_184_);
lean_dec(v_x_133_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_205_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_ks_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_vs_185_);
v___x_190_ = v_reuseFailAlloc_204_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v_newNode_191_; uint8_t v___y_193_; size_t v___x_199_; uint8_t v___x_200_; 
v_newNode_191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_190_, v_x_136_, v_x_137_);
v___x_199_ = ((size_t)7ULL);
v___x_200_ = lean_usize_dec_le(v___x_199_, v_x_135_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_191_);
v___x_202_ = lean_unsigned_to_nat(4u);
v___x_203_ = lean_nat_dec_lt(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
v___y_193_ = v___x_203_;
goto v___jp_192_;
}
else
{
v___y_193_ = v___x_200_;
goto v___jp_192_;
}
v___jp_192_:
{
if (v___y_193_ == 0)
{
lean_object* v_ks_194_; lean_object* v_vs_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_ks_194_ = lean_ctor_get(v_newNode_191_, 0);
lean_inc_ref(v_ks_194_);
v_vs_195_ = lean_ctor_get(v_newNode_191_, 1);
lean_inc_ref(v_vs_195_);
lean_dec_ref(v_newNode_191_);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_135_, v_ks_194_, v_vs_195_, v___x_196_, v___x_197_);
lean_dec_ref(v_vs_195_);
lean_dec_ref(v_ks_194_);
return v___x_198_;
}
else
{
return v_newNode_191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t v_depth_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_i_209_, lean_object* v_entries_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_keys_207_);
v___x_212_ = lean_nat_dec_lt(v_i_209_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec(v_i_209_);
return v_entries_210_;
}
else
{
lean_object* v_k_213_; lean_object* v_v_214_; uint64_t v___x_215_; size_t v_h_216_; size_t v___x_217_; lean_object* v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v_h_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_k_213_ = lean_array_fget_borrowed(v_keys_207_, v_i_209_);
v_v_214_ = lean_array_fget_borrowed(v_vals_208_, v_i_209_);
v___x_215_ = l_Lean_instHashableMVarId_hash(v_k_213_);
v_h_216_ = lean_uint64_to_usize(v___x_215_);
v___x_217_ = ((size_t)5ULL);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_sub(v_depth_206_, v___x_219_);
v___x_221_ = lean_usize_mul(v___x_217_, v___x_220_);
v_h_222_ = lean_usize_shift_right(v_h_216_, v___x_221_);
v___x_223_ = lean_nat_add(v_i_209_, v___x_218_);
lean_dec(v_i_209_);
lean_inc(v_v_214_);
lean_inc(v_k_213_);
v___x_224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_210_, v_h_222_, v_depth_206_, v_k_213_, v_v_214_);
v_i_209_ = v___x_223_;
v_entries_210_ = v___x_224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_depth_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_i_229_, lean_object* v_entries_230_){
_start:
{
size_t v_depth_boxed_231_; lean_object* v_res_232_; 
v_depth_boxed_231_ = lean_unbox_usize(v_depth_226_);
lean_dec(v_depth_226_);
v_res_232_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_231_, v_keys_227_, v_vals_228_, v_i_229_, v_entries_230_);
lean_dec_ref(v_vals_228_);
lean_dec_ref(v_keys_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_17722__boxed_238_; size_t v_x_17723__boxed_239_; lean_object* v_res_240_; 
v_x_17722__boxed_238_ = lean_unbox_usize(v_x_234_);
lean_dec(v_x_234_);
v_x_17723__boxed_239_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_233_, v_x_17722__boxed_238_, v_x_17723__boxed_239_, v_x_236_, v_x_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
uint64_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; 
v___x_244_ = l_Lean_instHashableMVarId_hash(v_x_242_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_241_, v___x_245_, v___x_246_, v_x_242_, v_x_243_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_248_, lean_object* v_val_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_mctx_253_; lean_object* v_cache_254_; lean_object* v_zetaDeltaFVarIds_255_; lean_object* v_postponed_256_; lean_object* v_diag_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_285_; 
v___x_252_ = lean_st_ref_take(v___y_250_);
v_mctx_253_ = lean_ctor_get(v___x_252_, 0);
v_cache_254_ = lean_ctor_get(v___x_252_, 1);
v_zetaDeltaFVarIds_255_ = lean_ctor_get(v___x_252_, 2);
v_postponed_256_ = lean_ctor_get(v___x_252_, 3);
v_diag_257_ = lean_ctor_get(v___x_252_, 4);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_285_ == 0)
{
v___x_259_ = v___x_252_;
v_isShared_260_ = v_isSharedCheck_285_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_diag_257_);
lean_inc(v_postponed_256_);
lean_inc(v_zetaDeltaFVarIds_255_);
lean_inc(v_cache_254_);
lean_inc(v_mctx_253_);
lean_dec(v___x_252_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_285_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_depth_261_; lean_object* v_levelAssignDepth_262_; lean_object* v_lmvarCounter_263_; lean_object* v_mvarCounter_264_; lean_object* v_lDecls_265_; lean_object* v_decls_266_; lean_object* v_userNames_267_; lean_object* v_lAssignment_268_; lean_object* v_eAssignment_269_; lean_object* v_dAssignment_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_284_; 
v_depth_261_ = lean_ctor_get(v_mctx_253_, 0);
v_levelAssignDepth_262_ = lean_ctor_get(v_mctx_253_, 1);
v_lmvarCounter_263_ = lean_ctor_get(v_mctx_253_, 2);
v_mvarCounter_264_ = lean_ctor_get(v_mctx_253_, 3);
v_lDecls_265_ = lean_ctor_get(v_mctx_253_, 4);
v_decls_266_ = lean_ctor_get(v_mctx_253_, 5);
v_userNames_267_ = lean_ctor_get(v_mctx_253_, 6);
v_lAssignment_268_ = lean_ctor_get(v_mctx_253_, 7);
v_eAssignment_269_ = lean_ctor_get(v_mctx_253_, 8);
v_dAssignment_270_ = lean_ctor_get(v_mctx_253_, 9);
v_isSharedCheck_284_ = !lean_is_exclusive(v_mctx_253_);
if (v_isSharedCheck_284_ == 0)
{
v___x_272_ = v_mctx_253_;
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_dAssignment_270_);
lean_inc(v_eAssignment_269_);
lean_inc(v_lAssignment_268_);
lean_inc(v_userNames_267_);
lean_inc(v_decls_266_);
lean_inc(v_lDecls_265_);
lean_inc(v_mvarCounter_264_);
lean_inc(v_lmvarCounter_263_);
lean_inc(v_levelAssignDepth_262_);
lean_inc(v_depth_261_);
lean_dec(v_mctx_253_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_269_, v_mvarId_248_, v_val_249_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 8, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_depth_261_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_levelAssignDepth_262_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_lmvarCounter_263_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_mvarCounter_264_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_lDecls_265_);
lean_ctor_set(v_reuseFailAlloc_283_, 5, v_decls_266_);
lean_ctor_set(v_reuseFailAlloc_283_, 6, v_userNames_267_);
lean_ctor_set(v_reuseFailAlloc_283_, 7, v_lAssignment_268_);
lean_ctor_set(v_reuseFailAlloc_283_, 8, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_283_, 9, v_dAssignment_270_);
v___x_276_ = v_reuseFailAlloc_283_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_276_);
v___x_278_ = v___x_259_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_cache_254_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_zetaDeltaFVarIds_255_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_postponed_256_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_diag_257_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_st_ref_set(v___y_250_, v___x_278_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_286_, lean_object* v_val_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_286_, v_val_287_, v___y_288_);
lean_dec(v___y_288_);
return v_res_290_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4(void){
_start:
{
uint8_t v___x_302_; uint64_t v___x_303_; 
v___x_302_ = 1;
v___x_303_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(lean_object* v___f_304_, lean_object* v_mv_305_, lean_object* v_val_306_, lean_object* v_tac_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_fileName_361_; lean_object* v_fileMap_362_; lean_object* v_options_363_; lean_object* v_currRecDepth_364_; lean_object* v_maxRecDepth_365_; lean_object* v_ref_366_; lean_object* v_currNamespace_367_; lean_object* v_openDecls_368_; lean_object* v_initHeartbeats_369_; lean_object* v_maxHeartbeats_370_; lean_object* v_quotContext_371_; lean_object* v_currMacroScope_372_; uint8_t v_diag_373_; lean_object* v_cancelTk_x3f_374_; uint8_t v_suppressElabErrors_375_; lean_object* v_inheritedTraceOptions_376_; lean_object* v___x_377_; uint8_t v_foApprox_378_; uint8_t v_ctxApprox_379_; uint8_t v_quasiPatternApprox_380_; uint8_t v_constApprox_381_; uint8_t v_isDefEqStuckEx_382_; uint8_t v_unificationHints_383_; uint8_t v_proofIrrelevance_384_; uint8_t v_assignSyntheticOpaque_385_; uint8_t v_offsetCnstrs_386_; uint8_t v_etaStruct_387_; uint8_t v_univApprox_388_; uint8_t v_iota_389_; uint8_t v_beta_390_; uint8_t v_proj_391_; uint8_t v_zeta_392_; uint8_t v_zetaDelta_393_; uint8_t v_zetaUnused_394_; uint8_t v_zetaHave_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_433_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_box(0);
v___x_317_ = 1;
v___x_321_ = lean_box(1);
v___x_322_ = 0;
v___x_359_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2));
v___x_360_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_360_, 0, v___x_315_);
lean_ctor_set(v___x_360_, 1, v___x_316_);
lean_ctor_set(v___x_360_, 2, v___x_315_);
lean_ctor_set(v___x_360_, 3, v___f_304_);
lean_ctor_set(v___x_360_, 4, v___x_321_);
lean_ctor_set(v___x_360_, 5, v___x_321_);
lean_ctor_set(v___x_360_, 6, v___x_315_);
lean_ctor_set(v___x_360_, 7, v___x_359_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8, v___x_317_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 1, v___x_317_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 2, v___x_317_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 3, v___x_317_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 4, v___x_322_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 5, v___x_322_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 6, v___x_322_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 7, v___x_322_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 8, v___x_317_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 9, v___x_322_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*8 + 10, v___x_317_);
v_fileName_361_ = lean_ctor_get(v___y_312_, 0);
v_fileMap_362_ = lean_ctor_get(v___y_312_, 1);
v_options_363_ = lean_ctor_get(v___y_312_, 2);
v_currRecDepth_364_ = lean_ctor_get(v___y_312_, 3);
v_maxRecDepth_365_ = lean_ctor_get(v___y_312_, 4);
v_ref_366_ = lean_ctor_get(v___y_312_, 5);
v_currNamespace_367_ = lean_ctor_get(v___y_312_, 6);
v_openDecls_368_ = lean_ctor_get(v___y_312_, 7);
v_initHeartbeats_369_ = lean_ctor_get(v___y_312_, 8);
v_maxHeartbeats_370_ = lean_ctor_get(v___y_312_, 9);
v_quotContext_371_ = lean_ctor_get(v___y_312_, 10);
v_currMacroScope_372_ = lean_ctor_get(v___y_312_, 11);
v_diag_373_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*14);
v_cancelTk_x3f_374_ = lean_ctor_get(v___y_312_, 12);
v_suppressElabErrors_375_ = lean_ctor_get_uint8(v___y_312_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_376_ = lean_ctor_get(v___y_312_, 13);
v___x_377_ = l_Lean_Meta_Context_config(v___y_310_);
v_foApprox_378_ = lean_ctor_get_uint8(v___x_377_, 0);
v_ctxApprox_379_ = lean_ctor_get_uint8(v___x_377_, 1);
v_quasiPatternApprox_380_ = lean_ctor_get_uint8(v___x_377_, 2);
v_constApprox_381_ = lean_ctor_get_uint8(v___x_377_, 3);
v_isDefEqStuckEx_382_ = lean_ctor_get_uint8(v___x_377_, 4);
v_unificationHints_383_ = lean_ctor_get_uint8(v___x_377_, 5);
v_proofIrrelevance_384_ = lean_ctor_get_uint8(v___x_377_, 6);
v_assignSyntheticOpaque_385_ = lean_ctor_get_uint8(v___x_377_, 7);
v_offsetCnstrs_386_ = lean_ctor_get_uint8(v___x_377_, 8);
v_etaStruct_387_ = lean_ctor_get_uint8(v___x_377_, 10);
v_univApprox_388_ = lean_ctor_get_uint8(v___x_377_, 11);
v_iota_389_ = lean_ctor_get_uint8(v___x_377_, 12);
v_beta_390_ = lean_ctor_get_uint8(v___x_377_, 13);
v_proj_391_ = lean_ctor_get_uint8(v___x_377_, 14);
v_zeta_392_ = lean_ctor_get_uint8(v___x_377_, 15);
v_zetaDelta_393_ = lean_ctor_get_uint8(v___x_377_, 16);
v_zetaUnused_394_ = lean_ctor_get_uint8(v___x_377_, 17);
v_zetaHave_395_ = lean_ctor_get_uint8(v___x_377_, 18);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_433_ == 0)
{
v___x_397_ = v___x_377_;
v_isShared_398_ = v_isSharedCheck_433_;
goto v_resetjp_396_;
}
else
{
lean_dec(v___x_377_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_433_;
goto v_resetjp_396_;
}
v___jp_318_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0));
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
v___jp_323_:
{
lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_358_; 
v___x_324_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mv_305_, v___y_311_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_358_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_358_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_358_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; 
v___x_329_ = lean_unbox(v_a_325_);
lean_dec(v_a_325_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_dec(v_mv_305_);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_object* v___x_334_; lean_object* v_a_335_; 
lean_del_object(v___x_327_);
v___x_334_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mv_305_, v___y_311_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref(v___x_334_);
if (lean_obj_tag(v_a_335_) == 1)
{
lean_object* v_val_336_; lean_object* v___x_337_; 
v_val_336_ = lean_ctor_get(v_a_335_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v_a_335_, 1);
v___x_337_ = l_Lean_Meta_Sym_unfoldReducible(v_val_336_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_338_, v___y_309_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mv_305_, v_a_340_, v___y_311_);
lean_dec_ref(v___x_341_);
goto v___jp_318_;
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_mv_305_);
v_a_342_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_339_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_mv_305_);
v_a_350_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_337_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_dec(v_a_335_);
lean_dec(v_mv_305_);
goto v___jp_318_;
}
}
}
}
v_resetjp_396_:
{
uint8_t v_trackZetaDelta_399_; lean_object* v_zetaDeltaSet_400_; lean_object* v_lctx_401_; lean_object* v_localInstances_402_; lean_object* v_defEqCtx_x3f_403_; lean_object* v_synthPendingDepth_404_; lean_object* v_canUnfold_x3f_405_; uint8_t v_univApprox_406_; uint8_t v_inTypeClassResolution_407_; uint8_t v_cacheInferType_408_; uint8_t v___x_409_; lean_object* v_config_411_; 
v_trackZetaDelta_399_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*7);
v_zetaDeltaSet_400_ = lean_ctor_get(v___y_310_, 1);
v_lctx_401_ = lean_ctor_get(v___y_310_, 2);
v_localInstances_402_ = lean_ctor_get(v___y_310_, 3);
v_defEqCtx_x3f_403_ = lean_ctor_get(v___y_310_, 4);
v_synthPendingDepth_404_ = lean_ctor_get(v___y_310_, 5);
v_canUnfold_x3f_405_ = lean_ctor_get(v___y_310_, 6);
v_univApprox_406_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_407_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*7 + 2);
v_cacheInferType_408_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*7 + 3);
v___x_409_ = 1;
if (v_isShared_398_ == 0)
{
v_config_411_ = v___x_397_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 0, v_foApprox_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 1, v_ctxApprox_379_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 2, v_quasiPatternApprox_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 3, v_constApprox_381_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 4, v_isDefEqStuckEx_382_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 5, v_unificationHints_383_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 6, v_proofIrrelevance_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 7, v_assignSyntheticOpaque_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 8, v_offsetCnstrs_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 10, v_etaStruct_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 11, v_univApprox_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 12, v_iota_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 13, v_beta_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 14, v_proj_391_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 15, v_zeta_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 16, v_zetaDelta_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 17, v_zetaUnused_394_);
lean_ctor_set_uint8(v_reuseFailAlloc_432_, 18, v_zetaHave_395_);
v_config_411_ = v_reuseFailAlloc_432_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; lean_object* v___x_415_; lean_object* v_ref_416_; lean_object* v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v_key_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_ctor_set_uint8(v_config_411_, 9, v___x_409_);
v___x_412_ = l_Lean_Meta_Context_configKey(v___y_310_);
v___x_413_ = 3ULL;
v___x_414_ = lean_uint64_shift_right(v___x_412_, v___x_413_);
v___x_415_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__3));
v_ref_416_ = l_Lean_replaceRef(v_val_306_, v_ref_366_);
lean_inc_ref(v_inheritedTraceOptions_376_);
lean_inc(v_cancelTk_x3f_374_);
lean_inc(v_currMacroScope_372_);
lean_inc(v_quotContext_371_);
lean_inc(v_maxHeartbeats_370_);
lean_inc(v_initHeartbeats_369_);
lean_inc(v_openDecls_368_);
lean_inc(v_currNamespace_367_);
lean_inc(v_maxRecDepth_365_);
lean_inc(v_currRecDepth_364_);
lean_inc_ref(v_options_363_);
lean_inc_ref(v_fileMap_362_);
lean_inc_ref(v_fileName_361_);
v___x_417_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_417_, 0, v_fileName_361_);
lean_ctor_set(v___x_417_, 1, v_fileMap_362_);
lean_ctor_set(v___x_417_, 2, v_options_363_);
lean_ctor_set(v___x_417_, 3, v_currRecDepth_364_);
lean_ctor_set(v___x_417_, 4, v_maxRecDepth_365_);
lean_ctor_set(v___x_417_, 5, v_ref_416_);
lean_ctor_set(v___x_417_, 6, v_currNamespace_367_);
lean_ctor_set(v___x_417_, 7, v_openDecls_368_);
lean_ctor_set(v___x_417_, 8, v_initHeartbeats_369_);
lean_ctor_set(v___x_417_, 9, v_maxHeartbeats_370_);
lean_ctor_set(v___x_417_, 10, v_quotContext_371_);
lean_ctor_set(v___x_417_, 11, v_currMacroScope_372_);
lean_ctor_set(v___x_417_, 12, v_cancelTk_x3f_374_);
lean_ctor_set(v___x_417_, 13, v_inheritedTraceOptions_376_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*14, v_diag_373_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*14 + 1, v_suppressElabErrors_375_);
v___x_418_ = lean_uint64_shift_left(v___x_414_, v___x_413_);
v___x_419_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4);
v_key_420_ = lean_uint64_lor(v___x_418_, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_421_, 0, v_config_411_);
lean_ctor_set_uint64(v___x_421_, sizeof(void*)*1, v_key_420_);
lean_inc(v_canUnfold_x3f_405_);
lean_inc(v_synthPendingDepth_404_);
lean_inc(v_defEqCtx_x3f_403_);
lean_inc_ref(v_localInstances_402_);
lean_inc_ref(v_lctx_401_);
lean_inc(v_zetaDeltaSet_400_);
v___x_422_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_zetaDeltaSet_400_);
lean_ctor_set(v___x_422_, 2, v_lctx_401_);
lean_ctor_set(v___x_422_, 3, v_localInstances_402_);
lean_ctor_set(v___x_422_, 4, v_defEqCtx_x3f_403_);
lean_ctor_set(v___x_422_, 5, v_synthPendingDepth_404_);
lean_ctor_set(v___x_422_, 6, v_canUnfold_x3f_405_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*7, v_trackZetaDelta_399_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*7 + 1, v_univApprox_406_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*7 + 2, v_inTypeClassResolution_407_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*7 + 3, v_cacheInferType_408_);
lean_inc(v_mv_305_);
v___x_423_ = l_Lean_Elab_runTactic(v_mv_305_, v_tac_307_, v___x_360_, v___x_415_, v___x_422_, v___y_311_, v___x_417_, v___y_313_);
lean_dec_ref_known(v___x_417_, 14);
lean_dec_ref_known(v___x_422_, 7);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_dec_ref_known(v___x_423_, 1);
goto v___jp_323_;
}
else
{
if (lean_obj_tag(v___x_423_) == 0)
{
lean_dec_ref_known(v___x_423_, 1);
goto v___jp_323_;
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_mv_305_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_434_, lean_object* v_mv_435_, lean_object* v_val_436_, lean_object* v_tac_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_434_, v_mv_435_, v_val_436_, v_tac_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_val_436_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_box(0);
return v___x_448_;
}
else
{
lean_object* v_key_449_; lean_object* v_value_450_; lean_object* v_tail_451_; uint8_t v___x_452_; 
v_key_449_ = lean_ctor_get(v_x_447_, 0);
v_value_450_ = lean_ctor_get(v_x_447_, 1);
v_tail_451_ = lean_ctor_get(v_x_447_, 2);
v___x_452_ = lean_nat_dec_eq(v_key_449_, v_a_446_);
if (v___x_452_ == 0)
{
v_x_447_ = v_tail_451_;
goto _start;
}
else
{
lean_object* v___x_454_; 
lean_inc(v_value_450_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_value_450_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec(v_a_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_buckets_460_; lean_object* v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; uint64_t v_fold_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_buckets_460_ = lean_ctor_get(v_m_458_, 1);
v___x_461_ = lean_array_get_size(v_buckets_460_);
v___x_462_ = lean_uint64_of_nat(v_a_459_);
v___x_463_ = 32ULL;
v___x_464_ = lean_uint64_shift_right(v___x_462_, v___x_463_);
v_fold_465_ = lean_uint64_xor(v___x_462_, v___x_464_);
v___x_466_ = 16ULL;
v___x_467_ = lean_uint64_shift_right(v_fold_465_, v___x_466_);
v___x_468_ = lean_uint64_xor(v_fold_465_, v___x_467_);
v___x_469_ = lean_uint64_to_usize(v___x_468_);
v___x_470_ = lean_usize_of_nat(v___x_461_);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_sub(v___x_470_, v___x_471_);
v___x_473_ = lean_usize_land(v___x_469_, v___x_472_);
v___x_474_ = lean_array_uget_borrowed(v_buckets_460_, v___x_473_);
v___x_475_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_459_, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_m_476_);
return v_res_478_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Array_mkArray0(lean_box(0));
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object* v_invariantAlts_543_, lean_object* v_n_544_, lean_object* v_mv_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___y_554_; uint8_t v___y_555_; lean_object* v___y_560_; lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_543_, v_n_544_);
if (lean_obj_tag(v___x_573_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_645_; 
v_val_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_645_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_645_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_645_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___f_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___f_578_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0));
v___x_579_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5));
lean_inc(v_val_574_);
v___x_580_ = l_Lean_Syntax_isOfKind(v_val_574_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7));
lean_inc(v_val_574_);
v___x_582_ = l_Lean_Syntax_isOfKind(v_val_574_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec(v_val_574_);
lean_dec(v_mv_545_);
v___x_583_ = lean_box(v___x_582_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_583_);
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = l_Lean_Syntax_getArg(v_val_574_, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9));
lean_inc(v___x_588_);
v___x_590_ = l_Lean_Syntax_isOfKind(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec(v___x_588_);
lean_dec(v_val_574_);
lean_dec(v_mv_545_);
v___x_591_ = lean_box(v___x_590_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_591_);
v___x_593_ = v___x_576_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v_ref_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_args_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_576_);
v_ref_595_ = lean_ctor_get(v_a_550_, 5);
v___x_596_ = l_Lean_Syntax_getArg(v___x_588_, v___x_587_);
lean_dec(v___x_588_);
v___x_597_ = lean_unsigned_to_nat(3u);
v___x_598_ = l_Lean_Syntax_getArg(v_val_574_, v___x_597_);
v_args_599_ = l_Lean_Syntax_getArgs(v___x_596_);
lean_dec(v___x_596_);
v___x_600_ = l_Lean_SourceInfo_fromRef(v_ref_595_, v___x_580_);
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11));
v___x_602_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_600_, 11);
v___x_603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14));
v___x_605_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16));
v___x_606_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18));
v___x_607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20));
v___x_608_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21));
v___x_609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_600_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22);
v___x_611_ = l_Array_append___redArg(v___x_610_, v_args_599_);
lean_dec_ref(v_args_599_);
v___x_612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_612_, 0, v___x_600_);
lean_ctor_set(v___x_612_, 1, v___x_606_);
lean_ctor_set(v___x_612_, 2, v___x_611_);
v___x_613_ = l_Lean_Syntax_node2(v___x_600_, v___x_607_, v___x_609_, v___x_612_);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23));
v___x_615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_600_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_617_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25));
v___x_618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_600_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
v___x_619_ = l_Lean_Syntax_node2(v___x_600_, v___x_617_, v___x_618_, v___x_598_);
v___x_620_ = l_Lean_Syntax_node3(v___x_600_, v___x_606_, v___x_613_, v___x_615_, v___x_619_);
v___x_621_ = l_Lean_Syntax_node1(v___x_600_, v___x_605_, v___x_620_);
v___x_622_ = l_Lean_Syntax_node1(v___x_600_, v___x_604_, v___x_621_);
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26));
v___x_624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_600_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_Syntax_node3(v___x_600_, v___x_601_, v___x_603_, v___x_622_, v___x_624_);
v___x_626_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_578_, v_mv_545_, v_val_574_, v___x_625_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_val_574_);
v___y_560_ = v___x_626_;
goto v___jp_559_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = l_Lean_Syntax_getArg(v_val_574_, v___x_627_);
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28));
v___x_630_ = l_Lean_Syntax_isOfKind(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_633_; 
lean_dec(v_val_574_);
lean_dec(v_mv_545_);
v___x_631_ = lean_box(v___x_630_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_631_);
v___x_633_ = v___x_576_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v_ref_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_del_object(v___x_576_);
v_ref_635_ = lean_ctor_get(v_a_550_, 5);
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = l_Lean_Syntax_getArg(v_val_574_, v___x_636_);
v___x_638_ = 0;
v___x_639_ = l_Lean_SourceInfo_fromRef(v_ref_635_, v___x_638_);
v___x_640_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_641_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25));
lean_inc(v___x_639_);
v___x_642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
v___x_643_ = l_Lean_Syntax_node2(v___x_639_, v___x_641_, v___x_642_, v___x_637_);
v___x_644_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_578_, v_mv_545_, v_val_574_, v___x_643_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_val_574_);
v___y_560_ = v___x_644_;
goto v___jp_559_;
}
}
}
}
else
{
uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v___x_573_);
lean_dec(v_mv_545_);
v___x_646_ = 0;
v___x_647_ = lean_box(v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
v___jp_553_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec_ref(v___y_554_);
v___x_556_ = lean_box(v___y_555_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___y_554_);
return v___x_558_;
}
}
v___jp_559_:
{
if (lean_obj_tag(v___y_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_569_; 
v_a_561_ = lean_ctor_get(v___y_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___y_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_563_ = v___y_560_;
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___y_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_a_565_; lean_object* v___x_567_; 
v_a_565_ = lean_ctor_get(v_a_561_, 0);
lean_inc(v_a_565_);
lean_dec(v_a_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v_a_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___y_560_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___y_560_, 1);
v___x_571_ = l_Lean_Exception_isInterrupt(v_a_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
lean_inc(v_a_570_);
v___x_572_ = l_Lean_Exception_isRuntime(v_a_570_);
v___y_554_ = v_a_570_;
v___y_555_ = v___x_572_;
goto v___jp_553_;
}
else
{
v___y_554_ = v_a_570_;
v___y_555_ = v___x_571_;
goto v___jp_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_649_, lean_object* v_n_650_, lean_object* v_mv_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_649_, v_n_650_, v_mv_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_n_650_);
lean_dec_ref(v_invariantAlts_649_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_660_, lean_object* v_m_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_661_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_664_, lean_object* v_m_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(v_00_u03b2_664_, v_m_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_m_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_668_, v___y_672_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(v_mvarId_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v_mvarId_677_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_686_, lean_object* v_val_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_686_, v_val_687_, v___y_691_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_696_, lean_object* v_val_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(v_mvarId_696_, v_val_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_706_, lean_object* v_a_707_, lean_object* v_x_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_707_, v_x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_710_, lean_object* v_a_711_, lean_object* v_x_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_710_, v_a_711_, v_x_712_);
lean_dec(v_x_712_);
lean_dec(v_a_711_);
return v_res_713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_718_, v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_724_, v_x_725_, v_x_726_);
return v___x_727_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, size_t v_x_730_, lean_object* v_x_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_729_, v_x_730_, v_x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
size_t v_x_18666__boxed_737_; uint8_t v_res_738_; lean_object* v_r_739_; 
v_x_18666__boxed_737_ = lean_unbox_usize(v_x_735_);
lean_dec(v_x_735_);
v_res_738_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_733_, v_x_734_, v_x_18666__boxed_737_, v_x_736_);
lean_dec(v_x_736_);
lean_dec_ref(v_x_734_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_740_, lean_object* v_x_741_, size_t v_x_742_, size_t v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_741_, v_x_742_, v_x_743_, v_x_744_, v_x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
size_t v_x_18677__boxed_753_; size_t v_x_18678__boxed_754_; lean_object* v_res_755_; 
v_x_18677__boxed_753_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_x_18678__boxed_754_ = lean_unbox_usize(v_x_750_);
lean_dec(v_x_750_);
v_res_755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_747_, v_x_748_, v_x_18677__boxed_753_, v_x_18678__boxed_754_, v_x_751_, v_x_752_);
return v_res_755_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_756_, lean_object* v_keys_757_, lean_object* v_vals_758_, lean_object* v_heq_759_, lean_object* v_i_760_, lean_object* v_k_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_757_, v_i_760_, v_k_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_763_, lean_object* v_keys_764_, lean_object* v_vals_765_, lean_object* v_heq_766_, lean_object* v_i_767_, lean_object* v_k_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_763_, v_keys_764_, v_vals_765_, v_heq_766_, v_i_767_, v_k_768_);
lean_dec(v_k_768_);
lean_dec_ref(v_vals_765_);
lean_dec_ref(v_keys_764_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_771_, lean_object* v_n_772_, lean_object* v_k_773_, lean_object* v_v_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_772_, v_k_773_, v_v_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_776_, size_t v_depth_777_, lean_object* v_keys_778_, lean_object* v_vals_779_, lean_object* v_heq_780_, lean_object* v_i_781_, lean_object* v_entries_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_777_, v_keys_778_, v_vals_779_, v_i_781_, v_entries_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_784_, lean_object* v_depth_785_, lean_object* v_keys_786_, lean_object* v_vals_787_, lean_object* v_heq_788_, lean_object* v_i_789_, lean_object* v_entries_790_){
_start:
{
size_t v_depth_boxed_791_; lean_object* v_res_792_; 
v_depth_boxed_791_ = lean_unbox_usize(v_depth_785_);
lean_dec(v_depth_785_);
v_res_792_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_784_, v_depth_boxed_791_, v_keys_786_, v_vals_787_, v_heq_788_, v_i_789_, v_entries_790_);
lean_dec_ref(v_vals_787_);
lean_dec_ref(v_keys_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_794_, v_x_795_, v_x_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
uint8_t v___x_801_; 
v___x_801_ = 0;
return v___x_801_;
}
else
{
lean_object* v_key_802_; lean_object* v_tail_803_; uint8_t v___x_804_; 
v_key_802_ = lean_ctor_get(v_x_800_, 0);
v_tail_803_ = lean_ctor_get(v_x_800_, 2);
v___x_804_ = lean_nat_dec_eq(v_key_802_, v_a_799_);
if (v___x_804_ == 0)
{
v_x_800_ = v_tail_803_;
goto _start;
}
else
{
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_806_, lean_object* v_x_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_806_, v_x_807_);
lean_dec(v_x_807_);
lean_dec(v_a_806_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
return v_x_810_;
}
else
{
lean_object* v_key_812_; lean_object* v_value_813_; lean_object* v_tail_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_837_; 
v_key_812_ = lean_ctor_get(v_x_811_, 0);
v_value_813_ = lean_ctor_get(v_x_811_, 1);
v_tail_814_ = lean_ctor_get(v_x_811_, 2);
v_isSharedCheck_837_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_837_ == 0)
{
v___x_816_ = v_x_811_;
v_isShared_817_ = v_isSharedCheck_837_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_tail_814_);
lean_inc(v_value_813_);
lean_inc(v_key_812_);
lean_dec(v_x_811_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_837_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v_fold_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_818_ = lean_array_get_size(v_x_810_);
v___x_819_ = lean_uint64_of_nat(v_key_812_);
v___x_820_ = 32ULL;
v___x_821_ = lean_uint64_shift_right(v___x_819_, v___x_820_);
v_fold_822_ = lean_uint64_xor(v___x_819_, v___x_821_);
v___x_823_ = 16ULL;
v___x_824_ = lean_uint64_shift_right(v_fold_822_, v___x_823_);
v___x_825_ = lean_uint64_xor(v_fold_822_, v___x_824_);
v___x_826_ = lean_uint64_to_usize(v___x_825_);
v___x_827_ = lean_usize_of_nat(v___x_818_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_sub(v___x_827_, v___x_828_);
v___x_830_ = lean_usize_land(v___x_826_, v___x_829_);
v___x_831_ = lean_array_uget_borrowed(v_x_810_, v___x_830_);
lean_inc(v___x_831_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 2, v___x_831_);
v___x_833_ = v___x_816_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_key_812_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_value_813_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v___x_831_);
v___x_833_ = v_reuseFailAlloc_836_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_array_uset(v_x_810_, v___x_830_, v___x_833_);
v_x_810_ = v___x_834_;
v_x_811_ = v_tail_814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_838_, lean_object* v_source_839_, lean_object* v_target_840_){
_start:
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_array_get_size(v_source_839_);
v___x_842_ = lean_nat_dec_lt(v_i_838_, v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_source_839_);
lean_dec(v_i_838_);
return v_target_840_;
}
else
{
lean_object* v_es_843_; lean_object* v___x_844_; lean_object* v_source_845_; lean_object* v_target_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_es_843_ = lean_array_fget(v_source_839_, v_i_838_);
v___x_844_ = lean_box(0);
v_source_845_ = lean_array_fset(v_source_839_, v_i_838_, v___x_844_);
v_target_846_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_840_, v_es_843_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_i_838_, v___x_847_);
lean_dec(v_i_838_);
v_i_838_ = v___x_848_;
v_source_839_ = v_source_845_;
v_target_840_ = v_target_846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_nbuckets_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_851_ = lean_array_get_size(v_data_850_);
v___x_852_ = lean_unsigned_to_nat(2u);
v_nbuckets_853_ = lean_nat_mul(v___x_851_, v___x_852_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_box(0);
v___x_856_ = lean_mk_array(v_nbuckets_853_, v___x_855_);
v___x_857_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_854_, v_data_850_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_858_, lean_object* v_a_859_, lean_object* v_b_860_){
_start:
{
lean_object* v_size_861_; lean_object* v_buckets_862_; lean_object* v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v_fold_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v_bkt_876_; uint8_t v___x_877_; 
v_size_861_ = lean_ctor_get(v_m_858_, 0);
v_buckets_862_ = lean_ctor_get(v_m_858_, 1);
v___x_863_ = lean_array_get_size(v_buckets_862_);
v___x_864_ = lean_uint64_of_nat(v_a_859_);
v___x_865_ = 32ULL;
v___x_866_ = lean_uint64_shift_right(v___x_864_, v___x_865_);
v_fold_867_ = lean_uint64_xor(v___x_864_, v___x_866_);
v___x_868_ = 16ULL;
v___x_869_ = lean_uint64_shift_right(v_fold_867_, v___x_868_);
v___x_870_ = lean_uint64_xor(v_fold_867_, v___x_869_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = lean_usize_of_nat(v___x_863_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_sub(v___x_872_, v___x_873_);
v___x_875_ = lean_usize_land(v___x_871_, v___x_874_);
v_bkt_876_ = lean_array_uget_borrowed(v_buckets_862_, v___x_875_);
v___x_877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_859_, v_bkt_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_898_; 
lean_inc_ref(v_buckets_862_);
lean_inc(v_size_861_);
v_isSharedCheck_898_ = !lean_is_exclusive(v_m_858_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; lean_object* v_unused_900_; 
v_unused_899_ = lean_ctor_get(v_m_858_, 1);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_m_858_, 0);
lean_dec(v_unused_900_);
v___x_879_ = v_m_858_;
v_isShared_880_ = v_isSharedCheck_898_;
goto v_resetjp_878_;
}
else
{
lean_dec(v_m_858_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_898_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v_size_x27_882_; lean_object* v___x_883_; lean_object* v_buckets_x27_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_881_ = lean_unsigned_to_nat(1u);
v_size_x27_882_ = lean_nat_add(v_size_861_, v___x_881_);
lean_dec(v_size_861_);
lean_inc(v_bkt_876_);
v___x_883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_883_, 0, v_a_859_);
lean_ctor_set(v___x_883_, 1, v_b_860_);
lean_ctor_set(v___x_883_, 2, v_bkt_876_);
v_buckets_x27_884_ = lean_array_uset(v_buckets_862_, v___x_875_, v___x_883_);
v___x_885_ = lean_unsigned_to_nat(4u);
v___x_886_ = lean_nat_mul(v_size_x27_882_, v___x_885_);
v___x_887_ = lean_unsigned_to_nat(3u);
v___x_888_ = lean_nat_div(v___x_886_, v___x_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_array_get_size(v_buckets_x27_884_);
v___x_890_ = lean_nat_dec_le(v___x_888_, v___x_889_);
lean_dec(v___x_888_);
if (v___x_890_ == 0)
{
lean_object* v_val_891_; lean_object* v___x_893_; 
v_val_891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_884_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_val_891_);
lean_ctor_set(v___x_879_, 0, v_size_x27_882_);
v___x_893_ = v___x_879_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_size_x27_882_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_val_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v___x_896_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_buckets_x27_884_);
lean_ctor_set(v___x_879_, 0, v_size_x27_882_);
v___x_896_ = v___x_879_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_size_x27_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_buckets_x27_884_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_dec(v_b_860_);
lean_dec(v_a_859_);
return v_m_858_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_901_, lean_object* v_as_x27_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
if (lean_obj_tag(v_as_x27_902_) == 0)
{
lean_object* v___x_913_; 
lean_dec_ref(v___x_901_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v_b_903_);
return v___x_913_;
}
else
{
lean_object* v_head_914_; lean_object* v_tail_915_; lean_object* v___x_916_; 
v_head_914_ = lean_ctor_get(v_as_x27_902_, 0);
v_tail_915_ = lean_ctor_get(v_as_x27_902_, 1);
lean_inc(v_head_914_);
v___x_916_ = l_Lean_MVarId_getType(v_head_914_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; uint8_t v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
lean_inc_ref(v___x_901_);
v___x_918_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_901_, v_a_917_);
lean_dec(v_a_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_inc(v_head_914_);
v___x_919_ = lean_array_push(v_b_903_, v_head_914_);
v_as_x27_902_ = v_tail_915_;
v_b_903_ = v___x_919_;
goto _start;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_specBackwardRuleCache_923_; lean_object* v_splitBackwardRuleCache_924_; lean_object* v_latticeBackwardRuleCache_925_; lean_object* v_frameDB_x3f_926_; lean_object* v_invariants_927_; lean_object* v_vcs_928_; lean_object* v_simpState_929_; lean_object* v_fuel_930_; lean_object* v_inlineHandledInvariants_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_988_; 
v___x_921_ = lean_st_ref_get(v___y_905_);
v___x_922_ = lean_st_ref_take(v___y_905_);
v_specBackwardRuleCache_923_ = lean_ctor_get(v___x_922_, 0);
v_splitBackwardRuleCache_924_ = lean_ctor_get(v___x_922_, 1);
v_latticeBackwardRuleCache_925_ = lean_ctor_get(v___x_922_, 2);
v_frameDB_x3f_926_ = lean_ctor_get(v___x_922_, 3);
v_invariants_927_ = lean_ctor_get(v___x_922_, 4);
v_vcs_928_ = lean_ctor_get(v___x_922_, 5);
v_simpState_929_ = lean_ctor_get(v___x_922_, 6);
v_fuel_930_ = lean_ctor_get(v___x_922_, 7);
v_inlineHandledInvariants_931_ = lean_ctor_get(v___x_922_, 8);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_988_ == 0)
{
v___x_933_ = v___x_922_;
v_isShared_934_ = v_isSharedCheck_988_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_inlineHandledInvariants_931_);
lean_inc(v_fuel_930_);
lean_inc(v_simpState_929_);
lean_inc(v_vcs_928_);
lean_inc(v_invariants_927_);
lean_inc(v_frameDB_x3f_926_);
lean_inc(v_latticeBackwardRuleCache_925_);
lean_inc(v_splitBackwardRuleCache_924_);
lean_inc(v_specBackwardRuleCache_923_);
lean_dec(v___x_922_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_988_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_inc(v_head_914_);
v___x_935_ = lean_array_push(v_invariants_927_, v_head_914_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_specBackwardRuleCache_923_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_splitBackwardRuleCache_924_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_latticeBackwardRuleCache_925_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_frameDB_x3f_926_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_987_, 5, v_vcs_928_);
lean_ctor_set(v_reuseFailAlloc_987_, 6, v_simpState_929_);
lean_ctor_set(v_reuseFailAlloc_987_, 7, v_fuel_930_);
lean_ctor_set(v_reuseFailAlloc_987_, 8, v_inlineHandledInvariants_931_);
v___x_937_ = v_reuseFailAlloc_987_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v_invariants_939_; lean_object* v_invariantAlts_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_938_ = lean_st_ref_set(v___y_905_, v___x_937_);
v_invariants_939_ = lean_ctor_get(v___x_921_, 4);
lean_inc_ref(v_invariants_939_);
lean_dec(v___x_921_);
v_invariantAlts_940_ = lean_ctor_get(v___y_904_, 2);
v___x_941_ = lean_array_get_size(v_invariants_939_);
lean_dec_ref(v_invariants_939_);
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v___x_941_, v___x_942_);
lean_inc(v_head_914_);
v___x_944_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_940_, v___x_943_, v_head_914_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; uint8_t v___x_946_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = lean_unbox(v_a_945_);
lean_dec(v_a_945_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; lean_object* v___x_948_; 
lean_dec(v___x_943_);
v___x_947_ = 2;
lean_inc(v_head_914_);
v___x_948_ = l_Lean_MVarId_setKind___redArg(v_head_914_, v___x_947_, v___y_909_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_dec_ref_known(v___x_948_, 1);
v_as_x27_902_ = v_tail_915_;
goto _start;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_b_903_);
lean_dec_ref(v___x_901_);
v_a_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_958_; lean_object* v_specBackwardRuleCache_959_; lean_object* v_splitBackwardRuleCache_960_; lean_object* v_latticeBackwardRuleCache_961_; lean_object* v_frameDB_x3f_962_; lean_object* v_invariants_963_; lean_object* v_vcs_964_; lean_object* v_simpState_965_; lean_object* v_fuel_966_; lean_object* v_inlineHandledInvariants_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_978_; 
v___x_958_ = lean_st_ref_take(v___y_905_);
v_specBackwardRuleCache_959_ = lean_ctor_get(v___x_958_, 0);
v_splitBackwardRuleCache_960_ = lean_ctor_get(v___x_958_, 1);
v_latticeBackwardRuleCache_961_ = lean_ctor_get(v___x_958_, 2);
v_frameDB_x3f_962_ = lean_ctor_get(v___x_958_, 3);
v_invariants_963_ = lean_ctor_get(v___x_958_, 4);
v_vcs_964_ = lean_ctor_get(v___x_958_, 5);
v_simpState_965_ = lean_ctor_get(v___x_958_, 6);
v_fuel_966_ = lean_ctor_get(v___x_958_, 7);
v_inlineHandledInvariants_967_ = lean_ctor_get(v___x_958_, 8);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_978_ == 0)
{
v___x_969_ = v___x_958_;
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_inlineHandledInvariants_967_);
lean_inc(v_fuel_966_);
lean_inc(v_simpState_965_);
lean_inc(v_vcs_964_);
lean_inc(v_invariants_963_);
lean_inc(v_frameDB_x3f_962_);
lean_inc(v_latticeBackwardRuleCache_961_);
lean_inc(v_splitBackwardRuleCache_960_);
lean_inc(v_specBackwardRuleCache_959_);
lean_dec(v___x_958_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = lean_box(0);
v___x_972_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_967_, v___x_943_, v___x_971_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 8, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_specBackwardRuleCache_959_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_splitBackwardRuleCache_960_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_latticeBackwardRuleCache_961_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_frameDB_x3f_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_invariants_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 5, v_vcs_964_);
lean_ctor_set(v_reuseFailAlloc_977_, 6, v_simpState_965_);
lean_ctor_set(v_reuseFailAlloc_977_, 7, v_fuel_966_);
lean_ctor_set(v_reuseFailAlloc_977_, 8, v___x_972_);
v___x_974_ = v_reuseFailAlloc_977_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = lean_st_ref_set(v___y_905_, v___x_974_);
v_as_x27_902_ = v_tail_915_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v___x_943_);
lean_dec_ref(v_b_903_);
lean_dec_ref(v___x_901_);
v_a_979_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_944_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_944_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v_b_903_);
lean_dec_ref(v___x_901_);
v_a_989_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_916_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_916_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_997_, lean_object* v_as_x27_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_997_, v_as_x27_998_, v_b_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v_as_x27_998_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_env_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_st_ref_get(v_a_1023_);
v_env_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc_ref(v_env_1026_);
lean_dec(v___x_1025_);
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1028_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_1026_, v_subgoals_1012_, v___x_1027_, v_a_1013_, v_a_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_subgoals_1029_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1043_, lean_object* v_m_1044_, lean_object* v_a_1045_, lean_object* v_b_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1044_, v_a_1045_, v_b_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1048_, lean_object* v_as_1049_, lean_object* v_as_x27_1050_, lean_object* v_b_1051_, lean_object* v_a_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1048_, v_as_x27_1050_, v_b_1051_, v___y_1053_, v___y_1054_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1066_ = _args[0];
lean_object* v_as_1067_ = _args[1];
lean_object* v_as_x27_1068_ = _args[2];
lean_object* v_b_1069_ = _args[3];
lean_object* v_a_1070_ = _args[4];
lean_object* v___y_1071_ = _args[5];
lean_object* v___y_1072_ = _args[6];
lean_object* v___y_1073_ = _args[7];
lean_object* v___y_1074_ = _args[8];
lean_object* v___y_1075_ = _args[9];
lean_object* v___y_1076_ = _args[10];
lean_object* v___y_1077_ = _args[11];
lean_object* v___y_1078_ = _args[12];
lean_object* v___y_1079_ = _args[13];
lean_object* v___y_1080_ = _args[14];
lean_object* v___y_1081_ = _args[15];
lean_object* v___y_1082_ = _args[16];
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(v___x_1066_, v_as_1067_, v_as_x27_1068_, v_b_1069_, v_a_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_as_x27_1068_);
lean_dec(v_as_1067_);
return v_res_1083_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1084_, lean_object* v_a_1085_, lean_object* v_x_1086_){
_start:
{
uint8_t v___x_1087_; 
v___x_1087_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1088_, lean_object* v_a_1089_, lean_object* v_x_1090_){
_start:
{
uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_res_1091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1088_, v_a_1089_, v_x_1090_);
lean_dec(v_x_1090_);
lean_dec(v_a_1089_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1093_, lean_object* v_data_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1096_, lean_object* v_i_1097_, lean_object* v_source_1098_, lean_object* v_target_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1097_, v_source_1098_, v_target_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1102_, v_x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object* v_goal_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_toGoalState_1118_; lean_object* v_mvarId_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1218_; 
v_toGoalState_1118_ = lean_ctor_get(v_goal_1105_, 0);
v_mvarId_1119_ = lean_ctor_get(v_goal_1105_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_goal_1105_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1121_ = v_goal_1105_;
v_isShared_1122_ = v_isSharedCheck_1218_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_mvarId_1119_);
lean_inc(v_toGoalState_1118_);
lean_dec(v_goal_1105_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1218_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(v_mvarId_1119_, v_a_1106_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_a_1124_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_toGoalState_1118_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1124_);
v___x_1126_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v___x_1126_, v_a_1106_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1200_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1200_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1200_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_toGoalState_1132_; lean_object* v_mvarId_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1199_; 
v_toGoalState_1132_ = lean_ctor_get(v_a_1128_, 0);
v_mvarId_1133_ = lean_ctor_get(v_a_1128_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_a_1128_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1135_ = v_a_1128_;
v_isShared_1136_ = v_isSharedCheck_1199_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_mvarId_1133_);
lean_inc(v_toGoalState_1132_);
lean_dec(v_a_1128_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1199_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_mvarId_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v_inconsistent_1174_; 
v_inconsistent_1174_ = lean_ctor_get_uint8(v_toGoalState_1132_, sizeof(void*)*17);
if (v_inconsistent_1174_ == 0)
{
uint8_t v_trivial_1175_; 
lean_del_object(v___x_1130_);
v_trivial_1175_ = lean_ctor_get_uint8(v_a_1106_, sizeof(void*)*4);
if (v_trivial_1175_ == 0)
{
v_mvarId_1138_ = v_mvarId_1133_;
v___y_1139_ = v_a_1107_;
v___y_1140_ = v_a_1114_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_mvarId_1133_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1186_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
if (lean_obj_tag(v_a_1177_) == 1)
{
lean_object* v_val_1181_; 
lean_del_object(v___x_1179_);
v_val_1181_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_val_1181_);
lean_dec_ref_known(v_a_1177_, 1);
v_mvarId_1138_ = v_val_1181_;
v___y_1139_ = v_a_1107_;
v___y_1140_ = v_a_1114_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
lean_dec(v_a_1177_);
lean_del_object(v___x_1135_);
lean_dec_ref(v_toGoalState_1132_);
v___x_1182_ = lean_box(0);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_del_object(v___x_1135_);
lean_dec_ref(v_toGoalState_1132_);
v_a_1187_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1176_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1176_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
lean_del_object(v___x_1135_);
lean_dec(v_mvarId_1133_);
lean_dec_ref(v_toGoalState_1132_);
v___x_1195_ = lean_box(0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1195_);
v___x_1197_ = v___x_1130_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
v___jp_1137_:
{
uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = 2;
lean_inc(v_mvarId_1138_);
v___x_1142_ = l_Lean_MVarId_setKind___redArg(v_mvarId_1138_, v___x_1141_, v___y_1140_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1172_; 
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v___x_1142_, 0);
lean_dec(v_unused_1173_);
v___x_1144_ = v___x_1142_;
v_isShared_1145_ = v_isSharedCheck_1172_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v___x_1142_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1172_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v_specBackwardRuleCache_1147_; lean_object* v_splitBackwardRuleCache_1148_; lean_object* v_latticeBackwardRuleCache_1149_; lean_object* v_frameDB_x3f_1150_; lean_object* v_invariants_1151_; lean_object* v_vcs_1152_; lean_object* v_simpState_1153_; lean_object* v_fuel_1154_; lean_object* v_inlineHandledInvariants_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1171_; 
v___x_1146_ = lean_st_ref_take(v___y_1139_);
v_specBackwardRuleCache_1147_ = lean_ctor_get(v___x_1146_, 0);
v_splitBackwardRuleCache_1148_ = lean_ctor_get(v___x_1146_, 1);
v_latticeBackwardRuleCache_1149_ = lean_ctor_get(v___x_1146_, 2);
v_frameDB_x3f_1150_ = lean_ctor_get(v___x_1146_, 3);
v_invariants_1151_ = lean_ctor_get(v___x_1146_, 4);
v_vcs_1152_ = lean_ctor_get(v___x_1146_, 5);
v_simpState_1153_ = lean_ctor_get(v___x_1146_, 6);
v_fuel_1154_ = lean_ctor_get(v___x_1146_, 7);
v_inlineHandledInvariants_1155_ = lean_ctor_get(v___x_1146_, 8);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1157_ = v___x_1146_;
v_isShared_1158_ = v_isSharedCheck_1171_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_inlineHandledInvariants_1155_);
lean_inc(v_fuel_1154_);
lean_inc(v_simpState_1153_);
lean_inc(v_vcs_1152_);
lean_inc(v_invariants_1151_);
lean_inc(v_frameDB_x3f_1150_);
lean_inc(v_latticeBackwardRuleCache_1149_);
lean_inc(v_splitBackwardRuleCache_1148_);
lean_inc(v_specBackwardRuleCache_1147_);
lean_dec(v___x_1146_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1171_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 1, v_mvarId_1138_);
v___x_1160_ = v___x_1135_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_toGoalState_1132_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_mvarId_1138_);
v___x_1160_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = lean_array_push(v_vcs_1152_, v___x_1160_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 5, v___x_1161_);
v___x_1163_ = v___x_1157_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_specBackwardRuleCache_1147_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_splitBackwardRuleCache_1148_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_latticeBackwardRuleCache_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_frameDB_x3f_1150_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_invariants_1151_);
lean_ctor_set(v_reuseFailAlloc_1169_, 5, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1169_, 6, v_simpState_1153_);
lean_ctor_set(v_reuseFailAlloc_1169_, 7, v_fuel_1154_);
lean_ctor_set(v_reuseFailAlloc_1169_, 8, v_inlineHandledInvariants_1155_);
v___x_1163_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_st_ref_set(v___y_1139_, v___x_1163_);
v___x_1165_ = lean_box(0);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1165_);
v___x_1167_ = v___x_1144_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
else
{
lean_dec(v_mvarId_1138_);
lean_del_object(v___x_1135_);
lean_dec_ref(v_toGoalState_1132_);
return v___x_1142_;
}
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1127_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1127_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1121_);
lean_dec_ref(v_toGoalState_1118_);
v_a_1210_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1123_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1123_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object* v_goal_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object* v_goal_1233_, lean_object* v_scope_1234_, size_t v_sz_1235_, size_t v_i_1236_, lean_object* v_bs_1237_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_lt(v_i_1236_, v_sz_1235_);
if (v___x_1238_ == 0)
{
lean_dec_ref(v_scope_1234_);
return v_bs_1237_;
}
else
{
lean_object* v_toGoalState_1239_; lean_object* v_v_1240_; lean_object* v___x_1241_; lean_object* v_bs_x27_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v_toGoalState_1239_ = lean_ctor_get(v_goal_1233_, 0);
v_v_1240_ = lean_array_uget(v_bs_1237_, v_i_1236_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v_bs_x27_1242_ = lean_array_uset(v_bs_1237_, v_i_1236_, v___x_1241_);
lean_inc_ref(v_toGoalState_1239_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_toGoalState_1239_);
lean_ctor_set(v___x_1243_, 1, v_v_1240_);
lean_inc_ref(v_scope_1234_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_scope_1234_);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1236_, v___x_1245_);
v___x_1247_ = lean_array_uset(v_bs_x27_1242_, v_i_1236_, v___x_1244_);
v_i_1236_ = v___x_1246_;
v_bs_1237_ = v___x_1247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object* v_goal_1249_, lean_object* v_scope_1250_, lean_object* v_sz_1251_, lean_object* v_i_1252_, lean_object* v_bs_1253_){
_start:
{
size_t v_sz_boxed_1254_; size_t v_i_boxed_1255_; lean_object* v_res_1256_; 
v_sz_boxed_1254_ = lean_unbox_usize(v_sz_1251_);
lean_dec(v_sz_1251_);
v_i_boxed_1255_ = lean_unbox_usize(v_i_1252_);
lean_dec(v_i_1252_);
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_goal_1249_, v_scope_1250_, v_sz_boxed_1254_, v_i_boxed_1255_, v_bs_1253_);
lean_dec_ref(v_goal_1249_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(lean_object* v_a_1257_, lean_object* v_scope_1258_, lean_object* v___x_1259_, lean_object* v_goal_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; size_t v_sz_1274_; size_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1273_ = l_Array_reverse___redArg(v_a_1257_);
v_sz_1274_ = lean_array_size(v___x_1273_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_goal_1260_, v_scope_1258_, v_sz_1274_, v___x_1275_, v___x_1273_);
v___x_1277_ = l_Array_append___redArg(v___x_1259_, v___x_1276_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0___boxed(lean_object* v_a_1280_, lean_object* v_scope_1281_, lean_object* v___x_1282_, lean_object* v_goal_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1280_, v_scope_1281_, v___x_1282_, v_goal_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_goal_1283_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(lean_object* v_a_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___y_1311_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1331_ = lean_array_get_size(v_a_1297_);
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_sub(v___x_1331_, v___x_1332_);
v___x_1334_ = lean_nat_dec_lt(v___x_1333_, v___x_1331_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_dec(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1297_);
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; lean_object* v_goal_1337_; lean_object* v_toGoalState_1338_; lean_object* v_scope_1339_; lean_object* v_mvarId_1340_; uint8_t v_inconsistent_1341_; lean_object* v___x_1342_; 
v___x_1336_ = lean_array_fget_borrowed(v_a_1297_, v___x_1333_);
lean_dec(v___x_1333_);
v_goal_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_ref(v_goal_1337_);
v_toGoalState_1338_ = lean_ctor_get(v_goal_1337_, 0);
v_scope_1339_ = lean_ctor_get(v___x_1336_, 1);
lean_inc_ref(v_scope_1339_);
v_mvarId_1340_ = lean_ctor_get(v_goal_1337_, 1);
v_inconsistent_1341_ = lean_ctor_get_uint8(v_toGoalState_1338_, sizeof(void*)*17);
v___x_1342_ = lean_array_pop(v_a_1297_);
if (v_inconsistent_1341_ == 0)
{
lean_object* v___x_1343_; 
lean_inc(v_mvarId_1340_);
v___x_1343_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_1339_, v_mvarId_1340_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
if (lean_obj_tag(v_a_1344_) == 0)
{
lean_object* v_scope_1345_; lean_object* v_subgoals_1346_; lean_object* v___x_1347_; 
v_scope_1345_ = lean_ctor_get(v_a_1344_, 0);
lean_inc_ref(v_scope_1345_);
v_subgoals_1346_ = lean_ctor_get(v_a_1344_, 1);
lean_inc(v_subgoals_1346_);
lean_dec_ref_known(v_a_1344_, 2);
v___x_1347_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1346_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v_subgoals_1346_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = lean_array_get_size(v_a_1348_);
v___x_1350_ = lean_nat_dec_lt(v___x_1332_, v___x_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1348_, v_scope_1345_, v___x_1342_, v_goal_1337_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec_ref(v_goal_1337_);
v___y_1311_ = v___x_1351_;
goto v___jp_1310_;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_1337_, v___y_1298_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1348_, v_scope_1345_, v___x_1342_, v_a_1353_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v_a_1353_);
v___y_1311_ = v___x_1354_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1348_);
lean_dec_ref(v_scope_1345_);
lean_dec_ref(v___x_1342_);
v_a_1355_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1352_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v_scope_1345_);
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_goal_1337_);
v_a_1363_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1347_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1347_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v___x_1371_; 
lean_dec_ref_known(v_a_1344_, 1);
v___x_1371_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1337_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_dec_ref_known(v___x_1371_, 1);
v_a_1297_ = v___x_1342_;
goto _start;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v___x_1342_);
v_a_1373_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1371_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1371_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___x_1342_);
lean_dec_ref(v_goal_1337_);
v_a_1381_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1343_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1343_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1339_);
lean_dec_ref(v_goal_1337_);
v_a_1297_ = v___x_1342_;
goto _start;
}
}
v___jp_1310_:
{
if (lean_obj_tag(v___y_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1322_; 
v_a_1312_ = lean_ctor_get(v___y_1311_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___y_1311_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1314_ = v___y_1311_;
v_isShared_1315_ = v_isSharedCheck_1322_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___y_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1322_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
if (lean_obj_tag(v_a_1312_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v_a_1312_, 1);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v_a_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
else
{
lean_object* v_a_1320_; 
lean_del_object(v___x_1314_);
v_a_1320_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v_a_1312_, 1);
v_a_1297_ = v_a_1320_;
goto _start;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1323_ = lean_ctor_get(v___y_1311_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___y_1311_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___y_1311_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___y_1311_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___boxed(lean_object* v_a_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v_a_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object* v_scope_1404_, lean_object* v_goal_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_toGoalState_1418_; lean_object* v_mvarId_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1458_; 
v_toGoalState_1418_ = lean_ctor_get(v_goal_1405_, 0);
v_mvarId_1419_ = lean_ctor_get(v_goal_1405_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_goal_1405_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1421_ = v_goal_1405_;
v_isShared_1422_ = v_isSharedCheck_1458_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_mvarId_1419_);
lean_inc(v_toGoalState_1418_);
lean_dec(v_goal_1405_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1458_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1419_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v_a_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_toGoalState_1418_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_a_1424_);
v___x_1426_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v_scope_1404_);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_mk_empty_array_with_capacity(v___x_1428_);
v___x_1430_ = lean_array_push(v___x_1429_, v___x_1427_);
v___x_1431_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v___x_1430_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v___x_1431_, 0);
lean_dec(v_unused_1440_);
v___x_1433_ = v___x_1431_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v___x_1431_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_box(0);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1431_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1431_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_del_object(v___x_1421_);
lean_dec_ref(v_toGoalState_1418_);
lean_dec_ref(v_scope_1404_);
v_a_1450_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1423_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1423_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object* v_scope_1459_, lean_object* v_goal_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_1459_, v_goal_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(lean_object* v_inst_1474_, lean_object* v_a_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v_a_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object* v_inst_1489_, lean_object* v_a_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_inst_1489_, v_a_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(lean_object* v_x_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___closed__0));
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___boxed(lean_object* v_x_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(v_x_1508_);
lean_dec(v_x_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_bs_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_bs_1513_);
return v___x_1517_;
}
else
{
lean_object* v_v_1518_; lean_object* v___x_1519_; lean_object* v_bs_x27_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_v_1518_ = lean_array_uget(v_bs_1513_, v_i_1512_);
v___x_1519_ = lean_unsigned_to_nat(0u);
v_bs_x27_1520_ = lean_array_uset(v_bs_1513_, v_i_1512_, v___x_1519_);
v___x_1521_ = lean_usize_to_nat(v_i_1512_);
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0));
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v___x_1521_, v___x_1523_);
lean_dec(v___x_1521_);
v___x_1525_ = l_Nat_reprFast(v___x_1524_);
v___x_1526_ = lean_string_append(v___x_1522_, v___x_1525_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = lean_box(0);
v___x_1528_ = l_Lean_Name_str___override(v___x_1527_, v___x_1526_);
v___x_1529_ = l_Lean_MVarId_setTag___redArg(v_v_1518_, v___x_1528_, v___y_1514_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1512_, v___x_1531_);
v___x_1533_ = lean_array_uset(v_bs_x27_1520_, v_i_1512_, v_a_1530_);
v_i_1512_ = v___x_1532_;
v_bs_1513_ = v___x_1533_;
goto _start;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_bs_x27_1520_);
v_a_1535_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1529_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1529_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(lean_object* v_sz_1543_, lean_object* v_i_1544_, lean_object* v_bs_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1543_);
lean_dec(v_sz_1543_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1544_);
lean_dec(v_i_1544_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_sz_boxed_1548_, v_i_boxed_1549_, v_bs_1545_, v___y_1546_);
lean_dec(v___y_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(size_t v_sz_1552_, size_t v_i_1553_, lean_object* v_bs_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1553_, v_sz_1552_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_bs_1554_);
return v___x_1561_;
}
else
{
lean_object* v_v_1562_; lean_object* v_mvarId_1563_; lean_object* v___x_1564_; 
v_v_1562_ = lean_array_uget_borrowed(v_bs_1554_, v_i_1553_);
v_mvarId_1563_ = lean_ctor_get(v_v_1562_, 1);
lean_inc_n(v_mvarId_1563_, 2);
v___x_1564_ = l_Lean_MVarId_getTag(v_mvarId_1563_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v_bs_x27_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = lean_unsigned_to_nat(0u);
v_bs_x27_1567_ = lean_array_uset(v_bs_1554_, v_i_1553_, v___x_1566_);
v___x_1568_ = lean_usize_to_nat(v_i_1553_);
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0));
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_add(v___x_1568_, v___x_1570_);
lean_dec(v___x_1568_);
v___x_1572_ = l_Nat_reprFast(v___x_1571_);
v___x_1573_ = lean_string_append(v___x_1569_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Lean_Name_str___override(v___x_1574_, v___x_1573_);
v___x_1576_ = lean_erase_macro_scopes(v_a_1565_);
v___x_1577_ = l_Lean_Name_append(v___x_1575_, v___x_1576_);
v___x_1578_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1563_, v___x_1577_, v___y_1556_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_add(v_i_1553_, v___x_1580_);
v___x_1582_ = lean_array_uset(v_bs_x27_1567_, v_i_1553_, v_a_1579_);
v_i_1553_ = v___x_1581_;
v_bs_1554_ = v___x_1582_;
goto _start;
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_bs_x27_1567_);
v_a_1584_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1578_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1578_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_mvarId_1563_);
lean_dec_ref(v_bs_1554_);
v_a_1592_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1564_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1564_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(v_sz_boxed_1608_, v_i_boxed_1609_, v_bs_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_mctx_1615_; lean_object* v_eAssignment_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = lean_st_ref_get(v___y_1612_);
v_mctx_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc_ref(v_mctx_1615_);
lean_dec(v___x_1614_);
v_eAssignment_1616_ = lean_ctor_get(v_mctx_1615_, 8);
lean_inc_ref(v_eAssignment_1616_);
lean_dec_ref(v_mctx_1615_);
v___x_1617_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1616_, v_mvarId_1611_);
lean_dec_ref(v_eAssignment_1616_);
v___x_1618_ = lean_box(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec(v_mvarId_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(lean_object* v_as_1624_, size_t v_i_1625_, size_t v_stop_1626_, lean_object* v_b_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_a_1639_; uint8_t v___x_1643_; 
v___x_1643_ = lean_usize_dec_eq(v_i_1625_, v_stop_1626_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; lean_object* v_mvarId_1647_; lean_object* v___x_1648_; 
v___x_1644_ = lean_array_uget_borrowed(v_as_1624_, v_i_1625_);
v_mvarId_1647_ = lean_ctor_get(v___x_1644_, 1);
v___x_1648_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1647_, v___y_1634_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; uint8_t v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
if (v___x_1650_ == 0)
{
goto v___jp_1645_;
}
else
{
v_a_1639_ = v_b_1627_;
goto v___jp_1638_;
}
}
else
{
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1651_; uint8_t v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1652_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
if (v___x_1652_ == 0)
{
v_a_1639_ = v_b_1627_;
goto v___jp_1638_;
}
else
{
goto v___jp_1645_;
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_b_1627_);
v_a_1653_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1648_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1648_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
v___jp_1645_:
{
lean_object* v___x_1646_; 
lean_inc(v___x_1644_);
v___x_1646_ = lean_array_push(v_b_1627_, v___x_1644_);
v_a_1639_ = v___x_1646_;
goto v___jp_1638_;
}
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_b_1627_);
return v___x_1661_;
}
v___jp_1638_:
{
size_t v___x_1640_; size_t v___x_1641_; 
v___x_1640_ = ((size_t)1ULL);
v___x_1641_ = lean_usize_add(v_i_1625_, v___x_1640_);
v_i_1625_ = v___x_1641_;
v_b_1627_ = v_a_1639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___boxed(lean_object* v_as_1662_, lean_object* v_i_1663_, lean_object* v_stop_1664_, lean_object* v_b_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
size_t v_i_boxed_1676_; size_t v_stop_boxed_1677_; lean_object* v_res_1678_; 
v_i_boxed_1676_ = lean_unbox_usize(v_i_1663_);
lean_dec(v_i_1663_);
v_stop_boxed_1677_ = lean_unbox_usize(v_stop_1664_);
lean_dec(v_stop_1664_);
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(v_as_1662_, v_i_boxed_1676_, v_stop_boxed_1677_, v_b_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v_as_1662_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1(lean_object* v_as_1679_, size_t v_i_1680_, size_t v_stop_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1680_, v_stop_1681_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; uint8_t v_retired_1690_; 
v___x_1689_ = lean_array_uget_borrowed(v_as_1679_, v_i_1680_);
v_retired_1690_ = lean_ctor_get_uint8(v___x_1689_, sizeof(void*)*4);
if (v_retired_1690_ == 0)
{
lean_object* v_frameStx_1691_; lean_object* v___x_1692_; 
v_frameStx_1691_ = lean_ctor_get(v___x_1689_, 2);
lean_inc(v_frameStx_1691_);
v___x_1692_ = lean_array_push(v_b_1682_, v_frameStx_1691_);
v___y_1684_ = v___x_1692_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v_b_1682_;
goto v___jp_1683_;
}
}
else
{
return v_b_1682_;
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1680_, v___x_1685_);
v_i_1680_ = v___x_1686_;
v_b_1682_ = v___y_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1___boxed(lean_object* v_as_1693_, lean_object* v_i_1694_, lean_object* v_stop_1695_, lean_object* v_b_1696_){
_start:
{
size_t v_i_boxed_1697_; size_t v_stop_boxed_1698_; lean_object* v_res_1699_; 
v_i_boxed_1697_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_stop_boxed_1698_ = lean_unbox_usize(v_stop_1695_);
lean_dec(v_stop_1695_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1(v_as_1693_, v_i_boxed_1697_, v_stop_boxed_1698_, v_b_1696_);
lean_dec_ref(v_as_1693_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object* v_as_1700_, lean_object* v_start_1701_, lean_object* v_stop_1702_){
_start:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___closed__0));
v___x_1704_ = lean_nat_dec_lt(v_start_1701_, v_stop_1702_);
if (v___x_1704_ == 0)
{
return v___x_1703_;
}
else
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = lean_array_get_size(v_as_1700_);
v___x_1706_ = lean_nat_dec_le(v_stop_1702_, v___x_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_nat_dec_lt(v_start_1701_, v___x_1705_);
if (v___x_1707_ == 0)
{
return v___x_1703_;
}
else
{
size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_usize_of_nat(v_start_1701_);
v___x_1709_ = lean_usize_of_nat(v___x_1705_);
v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1(v_as_1700_, v___x_1708_, v___x_1709_, v___x_1703_);
return v___x_1710_;
}
}
else
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_usize_of_nat(v_start_1701_);
v___x_1712_ = lean_usize_of_nat(v_stop_1702_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1_spec__1(v_as_1700_, v___x_1711_, v___x_1712_, v___x_1703_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object* v_as_1714_, lean_object* v_start_1715_, lean_object* v_stop_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(v_as_1714_, v_start_1715_, v_stop_1716_);
lean_dec(v_stop_1716_);
lean_dec(v_start_1715_);
lean_dec_ref(v_as_1714_);
return v_res_1717_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_unsigned_to_nat(16u);
v___x_1720_ = lean_mk_array(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3);
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v___x_1727_);
lean_ctor_set(v___x_1729_, 2, v___x_1727_);
lean_ctor_set(v___x_1729_, 3, v___x_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object* v_goal_1730_, lean_object* v_ctx_1731_, lean_object* v_scope_1732_, lean_object* v_stepLimit_x3f_1733_, lean_object* v_frameDB_x3f_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___x_1752_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v_a_1757_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___y_1783_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1);
v___x_1780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1781_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1733_) == 0)
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_box(1);
v___y_1783_ = v___x_1828_;
goto v___jp_1782_;
}
else
{
lean_object* v_val_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_val_1829_ = lean_ctor_get(v_stepLimit_x3f_1733_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_stepLimit_x3f_1733_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v_stepLimit_x3f_1733_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_val_1829_);
lean_dec(v_stepLimit_x3f_1733_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 0);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_val_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v___y_1783_ = v___x_1834_;
goto v___jp_1782_;
}
}
}
v___jp_1745_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1750_, 0, v___y_1746_);
lean_ctor_set(v___x_1750_, 1, v___y_1748_);
lean_ctor_set(v___x_1750_, 2, v___y_1747_);
lean_ctor_set(v___x_1750_, 3, v___y_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
v___jp_1753_:
{
if (lean_obj_tag(v___y_1755_) == 1)
{
lean_object* v_val_1758_; 
v_val_1758_ = lean_ctor_get(v___y_1755_, 0);
if (lean_obj_tag(v_val_1758_) == 1)
{
lean_object* v_value_1759_; lean_object* v_entries_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_inc_ref(v_val_1758_);
lean_dec_ref_known(v___y_1755_, 1);
v_value_1759_ = lean_ctor_get(v_val_1758_, 0);
lean_inc(v_value_1759_);
lean_dec_ref_known(v_val_1758_, 1);
v_entries_1760_ = lean_ctor_get(v_value_1759_, 1);
lean_inc_ref(v_entries_1760_);
lean_dec(v_value_1759_);
v___x_1761_ = lean_array_get_size(v_entries_1760_);
v___x_1762_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(v_entries_1760_, v___x_1752_, v___x_1761_);
lean_dec_ref(v_entries_1760_);
v___y_1746_ = v___y_1754_;
v___y_1747_ = v___y_1756_;
v___y_1748_ = v_a_1757_;
v___y_1749_ = v___x_1762_;
goto v___jp_1745_;
}
else
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(v___y_1755_);
lean_dec_ref_known(v___y_1755_, 1);
v___y_1746_ = v___y_1754_;
v___y_1747_ = v___y_1756_;
v___y_1748_ = v_a_1757_;
v___y_1749_ = v___x_1763_;
goto v___jp_1745_;
}
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(v___y_1755_);
lean_dec(v___y_1755_);
v___y_1746_ = v___y_1754_;
v___y_1747_ = v___y_1756_;
v___y_1748_ = v_a_1757_;
v___y_1749_ = v___x_1764_;
goto v___jp_1745_;
}
}
v___jp_1765_:
{
if (lean_obj_tag(v___y_1769_) == 0)
{
lean_object* v_a_1770_; 
v_a_1770_ = lean_ctor_get(v___y_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___y_1769_, 1);
v___y_1754_ = v___y_1766_;
v___y_1755_ = v___y_1767_;
v___y_1756_ = v___y_1768_;
v_a_1757_ = v_a_1770_;
goto v___jp_1753_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
v_a_1771_ = lean_ctor_get(v___y_1769_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___y_1769_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___y_1769_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___y_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
v___jp_1782_:
{
lean_object* v_initState_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_initState_1784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_initState_1784_, 0, v___x_1779_);
lean_ctor_set(v_initState_1784_, 1, v___x_1779_);
lean_ctor_set(v_initState_1784_, 2, v___x_1779_);
lean_ctor_set(v_initState_1784_, 3, v_frameDB_x3f_1734_);
lean_ctor_set(v_initState_1784_, 4, v___x_1780_);
lean_ctor_set(v_initState_1784_, 5, v___x_1780_);
lean_ctor_set(v_initState_1784_, 6, v___x_1781_);
lean_ctor_set(v_initState_1784_, 7, v___y_1783_);
lean_ctor_set(v_initState_1784_, 8, v___x_1779_);
v___x_1785_ = lean_st_mk_ref(v_initState_1784_);
v___x_1786_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_1732_, v_goal_1730_, v_ctx_1731_, v___x_1785_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; lean_object* v_frameDB_x3f_1788_; lean_object* v_invariants_1789_; lean_object* v_vcs_1790_; lean_object* v_inlineHandledInvariants_1791_; size_t v_sz_1792_; size_t v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref_known(v___x_1786_, 1);
v___x_1787_ = lean_st_ref_get(v___x_1785_);
lean_dec(v___x_1785_);
v_frameDB_x3f_1788_ = lean_ctor_get(v___x_1787_, 3);
lean_inc(v_frameDB_x3f_1788_);
v_invariants_1789_ = lean_ctor_get(v___x_1787_, 4);
lean_inc_ref_n(v_invariants_1789_, 2);
v_vcs_1790_ = lean_ctor_get(v___x_1787_, 5);
lean_inc_ref(v_vcs_1790_);
v_inlineHandledInvariants_1791_ = lean_ctor_get(v___x_1787_, 8);
lean_inc_ref(v_inlineHandledInvariants_1791_);
lean_dec(v___x_1787_);
v_sz_1792_ = lean_array_size(v_invariants_1789_);
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_sz_1792_, v___x_1793_, v_invariants_1789_, v_a_1741_);
if (lean_obj_tag(v___x_1794_) == 0)
{
size_t v_sz_1795_; lean_object* v___x_1796_; 
lean_dec_ref_known(v___x_1794_, 1);
v_sz_1795_ = lean_array_size(v_vcs_1790_);
lean_inc_ref(v_vcs_1790_);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(v_sz_1795_, v___x_1793_, v_vcs_1790_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_dec_ref_known(v___x_1796_, 1);
v___x_1797_ = lean_array_get_size(v_vcs_1790_);
v___x_1798_ = lean_nat_dec_lt(v___x_1752_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec_ref(v_vcs_1790_);
v___y_1754_ = v_invariants_1789_;
v___y_1755_ = v_frameDB_x3f_1788_;
v___y_1756_ = v_inlineHandledInvariants_1791_;
v_a_1757_ = v___x_1780_;
goto v___jp_1753_;
}
else
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_nat_dec_le(v___x_1797_, v___x_1797_);
if (v___x_1799_ == 0)
{
if (v___x_1798_ == 0)
{
lean_dec_ref(v_vcs_1790_);
v___y_1754_ = v_invariants_1789_;
v___y_1755_ = v_frameDB_x3f_1788_;
v___y_1756_ = v_inlineHandledInvariants_1791_;
v_a_1757_ = v___x_1780_;
goto v___jp_1753_;
}
else
{
size_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_usize_of_nat(v___x_1797_);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(v_vcs_1790_, v___x_1793_, v___x_1800_, v___x_1780_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec_ref(v_vcs_1790_);
v___y_1766_ = v_invariants_1789_;
v___y_1767_ = v_frameDB_x3f_1788_;
v___y_1768_ = v_inlineHandledInvariants_1791_;
v___y_1769_ = v___x_1801_;
goto v___jp_1765_;
}
}
else
{
size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_usize_of_nat(v___x_1797_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(v_vcs_1790_, v___x_1793_, v___x_1802_, v___x_1780_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
lean_dec_ref(v_vcs_1790_);
v___y_1766_ = v_invariants_1789_;
v___y_1767_ = v_frameDB_x3f_1788_;
v___y_1768_ = v_inlineHandledInvariants_1791_;
v___y_1769_ = v___x_1803_;
goto v___jp_1765_;
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec_ref(v_inlineHandledInvariants_1791_);
lean_dec_ref(v_vcs_1790_);
lean_dec_ref(v_invariants_1789_);
lean_dec(v_frameDB_x3f_1788_);
v_a_1804_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1796_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1796_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_inlineHandledInvariants_1791_);
lean_dec_ref(v_vcs_1790_);
lean_dec_ref(v_invariants_1789_);
lean_dec(v_frameDB_x3f_1788_);
v_a_1812_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1794_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1794_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v___x_1785_);
v_a_1820_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1786_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1786_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object* v_goal_1837_, lean_object* v_ctx_1838_, lean_object* v_scope_1839_, lean_object* v_stepLimit_x3f_1840_, lean_object* v_frameDB_x3f_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_goal_1837_, v_ctx_1838_, v_scope_1839_, v_stepLimit_x3f_1840_, v_frameDB_x3f_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_ctx_1838_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object* v_mvarId_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1853_, v___y_1860_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(v_mvarId_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec(v_mvarId_1865_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object* v_as_1877_, size_t v_sz_1878_, size_t v_i_1879_, lean_object* v_bs_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_sz_1878_, v_i_1879_, v_bs_1880_, v___y_1887_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object* v_as_1892_, lean_object* v_sz_1893_, lean_object* v_i_1894_, lean_object* v_bs_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
size_t v_sz_boxed_1906_; size_t v_i_boxed_1907_; lean_object* v_res_1908_; 
v_sz_boxed_1906_ = lean_unbox_usize(v_sz_1893_);
lean_dec(v_sz_1893_);
v_i_boxed_1907_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(v_as_1892_, v_sz_boxed_1906_, v_i_boxed_1907_, v_bs_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v_as_1892_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object* v_as_1909_, size_t v_sz_1910_, size_t v_i_1911_, lean_object* v_bs_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(v_sz_1910_, v_i_1911_, v_bs_1912_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object* v_as_1924_, lean_object* v_sz_1925_, lean_object* v_i_1926_, lean_object* v_bs_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
size_t v_sz_boxed_1938_; size_t v_i_boxed_1939_; lean_object* v_res_1940_; 
v_sz_boxed_1938_ = lean_unbox_usize(v_sz_1925_);
lean_dec(v_sz_1925_);
v_i_boxed_1939_ = lean_unbox_usize(v_i_1926_);
lean_dec(v_i_1926_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_as_1924_, v_sz_boxed_1938_, v_i_boxed_1939_, v_bs_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v_as_1924_);
return v_res_1940_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
}
#ifdef __cplusplus
}
#endif
