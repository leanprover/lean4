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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_50_; size_t v___x_51_; size_t v___x_52_; 
v___x_50_ = ((size_t)5ULL);
v___x_51_ = ((size_t)1ULL);
v___x_52_ = lean_usize_shift_left(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_53_; size_t v___x_54_; size_t v___x_55_; 
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_55_ = lean_usize_sub(v___x_54_, v___x_53_);
return v___x_55_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_56_, size_t v_x_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_56_) == 0)
{
lean_object* v_es_59_; lean_object* v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; lean_object* v_j_64_; lean_object* v___x_65_; 
v_es_59_ = lean_ctor_get(v_x_56_, 0);
v___x_60_ = lean_box(2);
v___x_61_ = ((size_t)5ULL);
v___x_62_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_63_ = lean_usize_land(v_x_57_, v___x_62_);
v_j_64_ = lean_usize_to_nat(v___x_63_);
v___x_65_ = lean_array_get_borrowed(v___x_60_, v_es_59_, v_j_64_);
lean_dec(v_j_64_);
switch(lean_obj_tag(v___x_65_))
{
case 0:
{
lean_object* v_key_66_; uint8_t v___x_67_; 
v_key_66_ = lean_ctor_get(v___x_65_, 0);
v___x_67_ = l_Lean_instBEqMVarId_beq(v_x_58_, v_key_66_);
return v___x_67_;
}
case 1:
{
lean_object* v_node_68_; size_t v___x_69_; 
v_node_68_ = lean_ctor_get(v___x_65_, 0);
v___x_69_ = lean_usize_shift_right(v_x_57_, v___x_61_);
v_x_56_ = v_node_68_;
v_x_57_ = v___x_69_;
goto _start;
}
default: 
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
else
{
lean_object* v_ks_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v_ks_72_ = lean_ctor_get(v_x_56_, 0);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_72_, v___x_73_, v_x_58_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_75_, lean_object* v_x_76_, lean_object* v_x_77_){
_start:
{
size_t v_x_17597__boxed_78_; uint8_t v_res_79_; lean_object* v_r_80_; 
v_x_17597__boxed_78_ = lean_unbox_usize(v_x_76_);
lean_dec(v_x_76_);
v_res_79_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_75_, v_x_17597__boxed_78_, v_x_77_);
lean_dec(v_x_77_);
lean_dec_ref(v_x_75_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint64_t v___x_83_; size_t v___x_84_; uint8_t v___x_85_; 
v___x_83_ = l_Lean_instHashableMVarId_hash(v_x_82_);
v___x_84_ = lean_uint64_to_usize(v___x_83_);
v___x_85_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_81_, v___x_84_, v_x_82_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_86_, v_x_87_);
lean_dec(v_x_87_);
lean_dec_ref(v_x_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_mctx_94_; lean_object* v_eAssignment_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_mctx_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_94_);
lean_dec(v___x_93_);
v_eAssignment_95_ = lean_ctor_get(v_mctx_94_, 8);
lean_inc_ref(v_eAssignment_95_);
lean_dec_ref(v_mctx_94_);
v___x_96_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_95_, v_mvarId_90_);
lean_dec_ref(v_eAssignment_95_);
v___x_97_ = lean_box(v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec(v_mvarId_99_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_x_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
lean_object* v_ks_107_; lean_object* v_vs_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_132_; 
v_ks_107_ = lean_ctor_get(v_x_103_, 0);
v_vs_108_ = lean_ctor_get(v_x_103_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_103_);
if (v_isSharedCheck_132_ == 0)
{
v___x_110_ = v_x_103_;
v_isShared_111_ = v_isSharedCheck_132_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_vs_108_);
lean_inc(v_ks_107_);
lean_dec(v_x_103_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_132_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_array_get_size(v_ks_107_);
v___x_113_ = lean_nat_dec_lt(v_x_104_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec(v_x_104_);
v___x_114_ = lean_array_push(v_ks_107_, v_x_105_);
v___x_115_ = lean_array_push(v_vs_108_, v_x_106_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_115_);
lean_ctor_set(v___x_110_, 0, v___x_114_);
v___x_117_ = v___x_110_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
else
{
lean_object* v_k_x27_119_; uint8_t v___x_120_; 
v_k_x27_119_ = lean_array_fget_borrowed(v_ks_107_, v_x_104_);
v___x_120_ = l_Lean_instBEqMVarId_beq(v_x_105_, v_k_x27_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_122_; 
if (v_isShared_111_ == 0)
{
v___x_122_ = v___x_110_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_ks_107_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_vs_108_);
v___x_122_ = v_reuseFailAlloc_126_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_x_104_, v___x_123_);
lean_dec(v_x_104_);
v_x_103_ = v___x_122_;
v_x_104_ = v___x_124_;
goto _start;
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = lean_array_fset(v_ks_107_, v_x_104_, v_x_105_);
v___x_128_ = lean_array_fset(v_vs_108_, v_x_104_, v_x_106_);
lean_dec(v_x_104_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 1, v___x_128_);
lean_ctor_set(v___x_110_, 0, v___x_127_);
v___x_130_ = v___x_110_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_n_133_, lean_object* v_k_134_, lean_object* v_v_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_n_133_, v___x_136_, v_k_134_, v_v_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object* v_x_139_, size_t v_x_140_, size_t v_x_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_es_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v_j_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_es_144_ = lean_ctor_get(v_x_139_, 0);
v___x_145_ = ((size_t)5ULL);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_148_ = lean_usize_land(v_x_140_, v___x_147_);
v_j_149_ = lean_usize_to_nat(v___x_148_);
v___x_150_ = lean_array_get_size(v_es_144_);
v___x_151_ = lean_nat_dec_lt(v_j_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_dec(v_j_149_);
lean_dec(v_x_143_);
lean_dec(v_x_142_);
return v_x_139_;
}
else
{
lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_188_; 
lean_inc_ref(v_es_144_);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_188_ == 0)
{
lean_object* v_unused_189_; 
v_unused_189_ = lean_ctor_get(v_x_139_, 0);
lean_dec(v_unused_189_);
v___x_153_ = v_x_139_;
v_isShared_154_ = v_isSharedCheck_188_;
goto v_resetjp_152_;
}
else
{
lean_dec(v_x_139_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_188_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_v_155_; lean_object* v___x_156_; lean_object* v_xs_x27_157_; lean_object* v___y_159_; 
v_v_155_ = lean_array_fget(v_es_144_, v_j_149_);
v___x_156_ = lean_box(0);
v_xs_x27_157_ = lean_array_fset(v_es_144_, v_j_149_, v___x_156_);
switch(lean_obj_tag(v_v_155_))
{
case 0:
{
lean_object* v_key_164_; lean_object* v_val_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_175_; 
v_key_164_ = lean_ctor_get(v_v_155_, 0);
v_val_165_ = lean_ctor_get(v_v_155_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_v_155_);
if (v_isSharedCheck_175_ == 0)
{
v___x_167_ = v_v_155_;
v_isShared_168_ = v_isSharedCheck_175_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_val_165_);
lean_inc(v_key_164_);
lean_dec(v_v_155_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_175_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
uint8_t v___x_169_; 
v___x_169_ = l_Lean_instBEqMVarId_beq(v_x_142_, v_key_164_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_del_object(v___x_167_);
v___x_170_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_164_, v_val_165_, v_x_142_, v_x_143_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
v___y_159_ = v___x_171_;
goto v___jp_158_;
}
else
{
lean_object* v___x_173_; 
lean_dec(v_val_165_);
lean_dec(v_key_164_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v_x_143_);
lean_ctor_set(v___x_167_, 0, v_x_142_);
v___x_173_ = v___x_167_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_x_142_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_x_143_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
v___y_159_ = v___x_173_;
goto v___jp_158_;
}
}
}
}
case 1:
{
lean_object* v_node_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_node_176_ = lean_ctor_get(v_v_155_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_v_155_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v_v_155_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_node_176_);
lean_dec(v_v_155_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_180_ = lean_usize_shift_right(v_x_140_, v___x_145_);
v___x_181_ = lean_usize_add(v_x_141_, v___x_146_);
v___x_182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_node_176_, v___x_180_, v___x_181_, v_x_142_, v_x_143_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_182_);
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
v___y_159_ = v___x_184_;
goto v___jp_158_;
}
}
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_x_142_);
lean_ctor_set(v___x_187_, 1, v_x_143_);
v___y_159_ = v___x_187_;
goto v___jp_158_;
}
}
v___jp_158_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_array_fset(v_xs_x27_157_, v_j_149_, v___y_159_);
lean_dec(v_j_149_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_160_);
v___x_162_ = v___x_153_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
else
{
lean_object* v_ks_190_; lean_object* v_vs_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_211_; 
v_ks_190_ = lean_ctor_get(v_x_139_, 0);
v_vs_191_ = lean_ctor_get(v_x_139_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_211_ == 0)
{
v___x_193_ = v_x_139_;
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_vs_191_);
lean_inc(v_ks_190_);
lean_dec(v_x_139_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_211_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_ks_190_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_vs_191_);
v___x_196_ = v_reuseFailAlloc_210_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v_newNode_197_; uint8_t v___y_199_; size_t v___x_205_; uint8_t v___x_206_; 
v_newNode_197_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_196_, v_x_142_, v_x_143_);
v___x_205_ = ((size_t)7ULL);
v___x_206_ = lean_usize_dec_le(v___x_205_, v_x_141_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_197_);
v___x_208_ = lean_unsigned_to_nat(4u);
v___x_209_ = lean_nat_dec_lt(v___x_207_, v___x_208_);
lean_dec(v___x_207_);
v___y_199_ = v___x_209_;
goto v___jp_198_;
}
else
{
v___y_199_ = v___x_206_;
goto v___jp_198_;
}
v___jp_198_:
{
if (v___y_199_ == 0)
{
lean_object* v_ks_200_; lean_object* v_vs_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_ks_200_ = lean_ctor_get(v_newNode_197_, 0);
lean_inc_ref(v_ks_200_);
v_vs_201_ = lean_ctor_get(v_newNode_197_, 1);
lean_inc_ref(v_vs_201_);
lean_dec_ref(v_newNode_197_);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_204_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_141_, v_ks_200_, v_vs_201_, v___x_202_, v___x_203_);
lean_dec_ref(v_vs_201_);
lean_dec_ref(v_ks_200_);
return v___x_204_;
}
else
{
return v_newNode_197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t v_depth_212_, lean_object* v_keys_213_, lean_object* v_vals_214_, lean_object* v_i_215_, lean_object* v_entries_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_array_get_size(v_keys_213_);
v___x_218_ = lean_nat_dec_lt(v_i_215_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec(v_i_215_);
return v_entries_216_;
}
else
{
lean_object* v_k_219_; lean_object* v_v_220_; uint64_t v___x_221_; size_t v_h_222_; size_t v___x_223_; lean_object* v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v_h_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_k_219_ = lean_array_fget_borrowed(v_keys_213_, v_i_215_);
v_v_220_ = lean_array_fget_borrowed(v_vals_214_, v_i_215_);
v___x_221_ = l_Lean_instHashableMVarId_hash(v_k_219_);
v_h_222_ = lean_uint64_to_usize(v___x_221_);
v___x_223_ = ((size_t)5ULL);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_sub(v_depth_212_, v___x_225_);
v___x_227_ = lean_usize_mul(v___x_223_, v___x_226_);
v_h_228_ = lean_usize_shift_right(v_h_222_, v___x_227_);
v___x_229_ = lean_nat_add(v_i_215_, v___x_224_);
lean_dec(v_i_215_);
lean_inc(v_v_220_);
lean_inc(v_k_219_);
v___x_230_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_216_, v_h_228_, v_depth_212_, v_k_219_, v_v_220_);
v_i_215_ = v___x_229_;
v_entries_216_ = v___x_230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_depth_232_, lean_object* v_keys_233_, lean_object* v_vals_234_, lean_object* v_i_235_, lean_object* v_entries_236_){
_start:
{
size_t v_depth_boxed_237_; lean_object* v_res_238_; 
v_depth_boxed_237_ = lean_unbox_usize(v_depth_232_);
lean_dec(v_depth_232_);
v_res_238_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_237_, v_keys_233_, v_vals_234_, v_i_235_, v_entries_236_);
lean_dec_ref(v_vals_234_);
lean_dec_ref(v_keys_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
size_t v_x_17752__boxed_244_; size_t v_x_17753__boxed_245_; lean_object* v_res_246_; 
v_x_17752__boxed_244_ = lean_unbox_usize(v_x_240_);
lean_dec(v_x_240_);
v_x_17753__boxed_245_ = lean_unbox_usize(v_x_241_);
lean_dec(v_x_241_);
v_res_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_239_, v_x_17752__boxed_244_, v_x_17753__boxed_245_, v_x_242_, v_x_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
uint64_t v___x_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
v___x_250_ = l_Lean_instHashableMVarId_hash(v_x_248_);
v___x_251_ = lean_uint64_to_usize(v___x_250_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_247_, v___x_251_, v___x_252_, v_x_248_, v_x_249_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_254_, lean_object* v_val_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_mctx_259_; lean_object* v_cache_260_; lean_object* v_zetaDeltaFVarIds_261_; lean_object* v_postponed_262_; lean_object* v_diag_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_291_; 
v___x_258_ = lean_st_ref_take(v___y_256_);
v_mctx_259_ = lean_ctor_get(v___x_258_, 0);
v_cache_260_ = lean_ctor_get(v___x_258_, 1);
v_zetaDeltaFVarIds_261_ = lean_ctor_get(v___x_258_, 2);
v_postponed_262_ = lean_ctor_get(v___x_258_, 3);
v_diag_263_ = lean_ctor_get(v___x_258_, 4);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_291_ == 0)
{
v___x_265_ = v___x_258_;
v_isShared_266_ = v_isSharedCheck_291_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_diag_263_);
lean_inc(v_postponed_262_);
lean_inc(v_zetaDeltaFVarIds_261_);
lean_inc(v_cache_260_);
lean_inc(v_mctx_259_);
lean_dec(v___x_258_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_291_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_depth_267_; lean_object* v_levelAssignDepth_268_; lean_object* v_lmvarCounter_269_; lean_object* v_mvarCounter_270_; lean_object* v_lDecls_271_; lean_object* v_decls_272_; lean_object* v_userNames_273_; lean_object* v_lAssignment_274_; lean_object* v_eAssignment_275_; lean_object* v_dAssignment_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_290_; 
v_depth_267_ = lean_ctor_get(v_mctx_259_, 0);
v_levelAssignDepth_268_ = lean_ctor_get(v_mctx_259_, 1);
v_lmvarCounter_269_ = lean_ctor_get(v_mctx_259_, 2);
v_mvarCounter_270_ = lean_ctor_get(v_mctx_259_, 3);
v_lDecls_271_ = lean_ctor_get(v_mctx_259_, 4);
v_decls_272_ = lean_ctor_get(v_mctx_259_, 5);
v_userNames_273_ = lean_ctor_get(v_mctx_259_, 6);
v_lAssignment_274_ = lean_ctor_get(v_mctx_259_, 7);
v_eAssignment_275_ = lean_ctor_get(v_mctx_259_, 8);
v_dAssignment_276_ = lean_ctor_get(v_mctx_259_, 9);
v_isSharedCheck_290_ = !lean_is_exclusive(v_mctx_259_);
if (v_isSharedCheck_290_ == 0)
{
v___x_278_ = v_mctx_259_;
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_dAssignment_276_);
lean_inc(v_eAssignment_275_);
lean_inc(v_lAssignment_274_);
lean_inc(v_userNames_273_);
lean_inc(v_decls_272_);
lean_inc(v_lDecls_271_);
lean_inc(v_mvarCounter_270_);
lean_inc(v_lmvarCounter_269_);
lean_inc(v_levelAssignDepth_268_);
lean_inc(v_depth_267_);
lean_dec(v_mctx_259_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_275_, v_mvarId_254_, v_val_255_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 8, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_depth_267_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_levelAssignDepth_268_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_lmvarCounter_269_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_mvarCounter_270_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_lDecls_271_);
lean_ctor_set(v_reuseFailAlloc_289_, 5, v_decls_272_);
lean_ctor_set(v_reuseFailAlloc_289_, 6, v_userNames_273_);
lean_ctor_set(v_reuseFailAlloc_289_, 7, v_lAssignment_274_);
lean_ctor_set(v_reuseFailAlloc_289_, 8, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_289_, 9, v_dAssignment_276_);
v___x_282_ = v_reuseFailAlloc_289_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_282_);
v___x_284_ = v___x_265_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_cache_260_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_zetaDeltaFVarIds_261_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_postponed_262_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_diag_263_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_st_ref_set(v___y_256_, v___x_284_);
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_292_, lean_object* v_val_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_292_, v_val_293_, v___y_294_);
lean_dec(v___y_294_);
return v_res_296_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4(void){
_start:
{
uint8_t v___x_308_; uint64_t v___x_309_; 
v___x_308_ = 1;
v___x_309_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(lean_object* v___f_310_, lean_object* v_mv_311_, lean_object* v_val_312_, lean_object* v_tac_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_fileName_367_; lean_object* v_fileMap_368_; lean_object* v_options_369_; lean_object* v_currRecDepth_370_; lean_object* v_maxRecDepth_371_; lean_object* v_ref_372_; lean_object* v_currNamespace_373_; lean_object* v_openDecls_374_; lean_object* v_initHeartbeats_375_; lean_object* v_maxHeartbeats_376_; lean_object* v_quotContext_377_; lean_object* v_currMacroScope_378_; uint8_t v_diag_379_; lean_object* v_cancelTk_x3f_380_; uint8_t v_suppressElabErrors_381_; lean_object* v_inheritedTraceOptions_382_; lean_object* v___x_383_; uint8_t v_foApprox_384_; uint8_t v_ctxApprox_385_; uint8_t v_quasiPatternApprox_386_; uint8_t v_constApprox_387_; uint8_t v_isDefEqStuckEx_388_; uint8_t v_unificationHints_389_; uint8_t v_proofIrrelevance_390_; uint8_t v_assignSyntheticOpaque_391_; uint8_t v_offsetCnstrs_392_; uint8_t v_etaStruct_393_; uint8_t v_univApprox_394_; uint8_t v_iota_395_; uint8_t v_beta_396_; uint8_t v_proj_397_; uint8_t v_zeta_398_; uint8_t v_zetaDelta_399_; uint8_t v_zetaUnused_400_; uint8_t v_zetaHave_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_439_; 
v___x_321_ = lean_box(0);
v___x_322_ = lean_box(0);
v___x_323_ = 1;
v___x_327_ = lean_box(1);
v___x_328_ = 0;
v___x_365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2));
v___x_366_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_366_, 0, v___x_321_);
lean_ctor_set(v___x_366_, 1, v___x_322_);
lean_ctor_set(v___x_366_, 2, v___x_321_);
lean_ctor_set(v___x_366_, 3, v___f_310_);
lean_ctor_set(v___x_366_, 4, v___x_327_);
lean_ctor_set(v___x_366_, 5, v___x_327_);
lean_ctor_set(v___x_366_, 6, v___x_321_);
lean_ctor_set(v___x_366_, 7, v___x_365_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8, v___x_323_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 1, v___x_323_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 2, v___x_323_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 3, v___x_323_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 4, v___x_328_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 5, v___x_328_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 6, v___x_328_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 7, v___x_328_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 8, v___x_323_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 9, v___x_328_);
lean_ctor_set_uint8(v___x_366_, sizeof(void*)*8 + 10, v___x_323_);
v_fileName_367_ = lean_ctor_get(v___y_318_, 0);
v_fileMap_368_ = lean_ctor_get(v___y_318_, 1);
v_options_369_ = lean_ctor_get(v___y_318_, 2);
v_currRecDepth_370_ = lean_ctor_get(v___y_318_, 3);
v_maxRecDepth_371_ = lean_ctor_get(v___y_318_, 4);
v_ref_372_ = lean_ctor_get(v___y_318_, 5);
v_currNamespace_373_ = lean_ctor_get(v___y_318_, 6);
v_openDecls_374_ = lean_ctor_get(v___y_318_, 7);
v_initHeartbeats_375_ = lean_ctor_get(v___y_318_, 8);
v_maxHeartbeats_376_ = lean_ctor_get(v___y_318_, 9);
v_quotContext_377_ = lean_ctor_get(v___y_318_, 10);
v_currMacroScope_378_ = lean_ctor_get(v___y_318_, 11);
v_diag_379_ = lean_ctor_get_uint8(v___y_318_, sizeof(void*)*14);
v_cancelTk_x3f_380_ = lean_ctor_get(v___y_318_, 12);
v_suppressElabErrors_381_ = lean_ctor_get_uint8(v___y_318_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_382_ = lean_ctor_get(v___y_318_, 13);
v___x_383_ = l_Lean_Meta_Context_config(v___y_316_);
v_foApprox_384_ = lean_ctor_get_uint8(v___x_383_, 0);
v_ctxApprox_385_ = lean_ctor_get_uint8(v___x_383_, 1);
v_quasiPatternApprox_386_ = lean_ctor_get_uint8(v___x_383_, 2);
v_constApprox_387_ = lean_ctor_get_uint8(v___x_383_, 3);
v_isDefEqStuckEx_388_ = lean_ctor_get_uint8(v___x_383_, 4);
v_unificationHints_389_ = lean_ctor_get_uint8(v___x_383_, 5);
v_proofIrrelevance_390_ = lean_ctor_get_uint8(v___x_383_, 6);
v_assignSyntheticOpaque_391_ = lean_ctor_get_uint8(v___x_383_, 7);
v_offsetCnstrs_392_ = lean_ctor_get_uint8(v___x_383_, 8);
v_etaStruct_393_ = lean_ctor_get_uint8(v___x_383_, 10);
v_univApprox_394_ = lean_ctor_get_uint8(v___x_383_, 11);
v_iota_395_ = lean_ctor_get_uint8(v___x_383_, 12);
v_beta_396_ = lean_ctor_get_uint8(v___x_383_, 13);
v_proj_397_ = lean_ctor_get_uint8(v___x_383_, 14);
v_zeta_398_ = lean_ctor_get_uint8(v___x_383_, 15);
v_zetaDelta_399_ = lean_ctor_get_uint8(v___x_383_, 16);
v_zetaUnused_400_ = lean_ctor_get_uint8(v___x_383_, 17);
v_zetaHave_401_ = lean_ctor_get_uint8(v___x_383_, 18);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_439_ == 0)
{
v___x_403_ = v___x_383_;
v_isShared_404_ = v_isSharedCheck_439_;
goto v_resetjp_402_;
}
else
{
lean_dec(v___x_383_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_439_;
goto v_resetjp_402_;
}
v___jp_324_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0));
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_364_; 
v___x_330_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mv_311_, v___y_317_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_364_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_364_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_364_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
uint8_t v___x_335_; 
v___x_335_ = lean_unbox(v_a_331_);
lean_dec(v_a_331_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec(v_mv_311_);
v___x_336_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v___x_340_; lean_object* v_a_341_; 
lean_del_object(v___x_333_);
v___x_340_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mv_311_, v___y_317_);
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
if (lean_obj_tag(v_a_341_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_343_; 
v_val_342_ = lean_ctor_get(v_a_341_, 0);
lean_inc(v_val_342_);
lean_dec_ref_known(v_a_341_, 1);
v___x_343_ = l_Lean_Meta_Sym_unfoldReducible(v_val_342_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_344_, v___y_315_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mv_311_, v_a_346_, v___y_317_);
lean_dec_ref(v___x_347_);
goto v___jp_324_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_mv_311_);
v_a_348_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_345_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_345_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_mv_311_);
v_a_356_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_343_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_343_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_dec(v_a_341_);
lean_dec(v_mv_311_);
goto v___jp_324_;
}
}
}
}
v_resetjp_402_:
{
uint8_t v_trackZetaDelta_405_; lean_object* v_zetaDeltaSet_406_; lean_object* v_lctx_407_; lean_object* v_localInstances_408_; lean_object* v_defEqCtx_x3f_409_; lean_object* v_synthPendingDepth_410_; lean_object* v_canUnfold_x3f_411_; uint8_t v_univApprox_412_; uint8_t v_inTypeClassResolution_413_; uint8_t v_cacheInferType_414_; uint8_t v___x_415_; lean_object* v_config_417_; 
v_trackZetaDelta_405_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*7);
v_zetaDeltaSet_406_ = lean_ctor_get(v___y_316_, 1);
v_lctx_407_ = lean_ctor_get(v___y_316_, 2);
v_localInstances_408_ = lean_ctor_get(v___y_316_, 3);
v_defEqCtx_x3f_409_ = lean_ctor_get(v___y_316_, 4);
v_synthPendingDepth_410_ = lean_ctor_get(v___y_316_, 5);
v_canUnfold_x3f_411_ = lean_ctor_get(v___y_316_, 6);
v_univApprox_412_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_413_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*7 + 2);
v_cacheInferType_414_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*7 + 3);
v___x_415_ = 1;
if (v_isShared_404_ == 0)
{
v_config_417_ = v___x_403_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 0, v_foApprox_384_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 1, v_ctxApprox_385_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 2, v_quasiPatternApprox_386_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 3, v_constApprox_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 4, v_isDefEqStuckEx_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 5, v_unificationHints_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 6, v_proofIrrelevance_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 7, v_assignSyntheticOpaque_391_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 8, v_offsetCnstrs_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 10, v_etaStruct_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 11, v_univApprox_394_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 12, v_iota_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 13, v_beta_396_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 14, v_proj_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 15, v_zeta_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 16, v_zetaDelta_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 17, v_zetaUnused_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, 18, v_zetaHave_401_);
v_config_417_ = v_reuseFailAlloc_438_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; lean_object* v___x_421_; lean_object* v_ref_422_; lean_object* v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v_key_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_ctor_set_uint8(v_config_417_, 9, v___x_415_);
v___x_418_ = l_Lean_Meta_Context_configKey(v___y_316_);
v___x_419_ = 3ULL;
v___x_420_ = lean_uint64_shift_right(v___x_418_, v___x_419_);
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__3));
v_ref_422_ = l_Lean_replaceRef(v_val_312_, v_ref_372_);
lean_inc_ref(v_inheritedTraceOptions_382_);
lean_inc(v_cancelTk_x3f_380_);
lean_inc(v_currMacroScope_378_);
lean_inc(v_quotContext_377_);
lean_inc(v_maxHeartbeats_376_);
lean_inc(v_initHeartbeats_375_);
lean_inc(v_openDecls_374_);
lean_inc(v_currNamespace_373_);
lean_inc(v_maxRecDepth_371_);
lean_inc(v_currRecDepth_370_);
lean_inc_ref(v_options_369_);
lean_inc_ref(v_fileMap_368_);
lean_inc_ref(v_fileName_367_);
v___x_423_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_423_, 0, v_fileName_367_);
lean_ctor_set(v___x_423_, 1, v_fileMap_368_);
lean_ctor_set(v___x_423_, 2, v_options_369_);
lean_ctor_set(v___x_423_, 3, v_currRecDepth_370_);
lean_ctor_set(v___x_423_, 4, v_maxRecDepth_371_);
lean_ctor_set(v___x_423_, 5, v_ref_422_);
lean_ctor_set(v___x_423_, 6, v_currNamespace_373_);
lean_ctor_set(v___x_423_, 7, v_openDecls_374_);
lean_ctor_set(v___x_423_, 8, v_initHeartbeats_375_);
lean_ctor_set(v___x_423_, 9, v_maxHeartbeats_376_);
lean_ctor_set(v___x_423_, 10, v_quotContext_377_);
lean_ctor_set(v___x_423_, 11, v_currMacroScope_378_);
lean_ctor_set(v___x_423_, 12, v_cancelTk_x3f_380_);
lean_ctor_set(v___x_423_, 13, v_inheritedTraceOptions_382_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*14, v_diag_379_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*14 + 1, v_suppressElabErrors_381_);
v___x_424_ = lean_uint64_shift_left(v___x_420_, v___x_419_);
v___x_425_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__4);
v_key_426_ = lean_uint64_lor(v___x_424_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_427_, 0, v_config_417_);
lean_ctor_set_uint64(v___x_427_, sizeof(void*)*1, v_key_426_);
lean_inc(v_canUnfold_x3f_411_);
lean_inc(v_synthPendingDepth_410_);
lean_inc(v_defEqCtx_x3f_409_);
lean_inc_ref(v_localInstances_408_);
lean_inc_ref(v_lctx_407_);
lean_inc(v_zetaDeltaSet_406_);
v___x_428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_zetaDeltaSet_406_);
lean_ctor_set(v___x_428_, 2, v_lctx_407_);
lean_ctor_set(v___x_428_, 3, v_localInstances_408_);
lean_ctor_set(v___x_428_, 4, v_defEqCtx_x3f_409_);
lean_ctor_set(v___x_428_, 5, v_synthPendingDepth_410_);
lean_ctor_set(v___x_428_, 6, v_canUnfold_x3f_411_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7, v_trackZetaDelta_405_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7 + 1, v_univApprox_412_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7 + 2, v_inTypeClassResolution_413_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*7 + 3, v_cacheInferType_414_);
lean_inc(v_mv_311_);
v___x_429_ = l_Lean_Elab_runTactic(v_mv_311_, v_tac_313_, v___x_366_, v___x_421_, v___x_428_, v___y_317_, v___x_423_, v___y_319_);
lean_dec_ref_known(v___x_423_, 14);
lean_dec_ref_known(v___x_428_, 7);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_dec_ref_known(v___x_429_, 1);
goto v___jp_329_;
}
else
{
if (lean_obj_tag(v___x_429_) == 0)
{
lean_dec_ref_known(v___x_429_, 1);
goto v___jp_329_;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_mv_311_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_440_, lean_object* v_mv_441_, lean_object* v_val_442_, lean_object* v_tac_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_440_, v_mv_441_, v_val_442_, v_tac_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v_val_442_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_452_, lean_object* v_x_453_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
lean_object* v_key_455_; lean_object* v_value_456_; lean_object* v_tail_457_; uint8_t v___x_458_; 
v_key_455_ = lean_ctor_get(v_x_453_, 0);
v_value_456_ = lean_ctor_get(v_x_453_, 1);
v_tail_457_ = lean_ctor_get(v_x_453_, 2);
v___x_458_ = lean_nat_dec_eq(v_key_455_, v_a_452_);
if (v___x_458_ == 0)
{
v_x_453_ = v_tail_457_;
goto _start;
}
else
{
lean_object* v___x_460_; 
lean_inc(v_value_456_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v_value_456_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_461_, v_x_462_);
lean_dec(v_x_462_);
lean_dec(v_a_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_buckets_466_; lean_object* v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v_fold_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_buckets_466_ = lean_ctor_get(v_m_464_, 1);
v___x_467_ = lean_array_get_size(v_buckets_466_);
v___x_468_ = lean_uint64_of_nat(v_a_465_);
v___x_469_ = 32ULL;
v___x_470_ = lean_uint64_shift_right(v___x_468_, v___x_469_);
v_fold_471_ = lean_uint64_xor(v___x_468_, v___x_470_);
v___x_472_ = 16ULL;
v___x_473_ = lean_uint64_shift_right(v_fold_471_, v___x_472_);
v___x_474_ = lean_uint64_xor(v_fold_471_, v___x_473_);
v___x_475_ = lean_uint64_to_usize(v___x_474_);
v___x_476_ = lean_usize_of_nat(v___x_467_);
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_sub(v___x_476_, v___x_477_);
v___x_479_ = lean_usize_land(v___x_475_, v___x_478_);
v___x_480_ = lean_array_uget_borrowed(v_buckets_466_, v___x_479_);
v___x_481_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_465_, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_m_482_);
return v_res_484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Array_mkArray0(lean_box(0));
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object* v_invariantAlts_549_, lean_object* v_n_550_, lean_object* v_mv_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___y_560_; uint8_t v___y_561_; lean_object* v___y_566_; lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_549_, v_n_550_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_651_; 
v_val_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_651_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_651_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_val_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_651_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___f_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___f_584_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0));
v___x_585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5));
lean_inc(v_val_580_);
v___x_586_ = l_Lean_Syntax_isOfKind(v_val_580_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7));
lean_inc(v_val_580_);
v___x_588_ = l_Lean_Syntax_isOfKind(v_val_580_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec(v_val_580_);
lean_dec(v_mv_551_);
v___x_589_ = lean_box(v___x_588_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
lean_ctor_set(v___x_582_, 0, v___x_589_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = l_Lean_Syntax_getArg(v_val_580_, v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9));
lean_inc(v___x_594_);
v___x_596_ = l_Lean_Syntax_isOfKind(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec(v___x_594_);
lean_dec(v_val_580_);
lean_dec(v_mv_551_);
v___x_597_ = lean_box(v___x_596_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
lean_ctor_set(v___x_582_, 0, v___x_597_);
v___x_599_ = v___x_582_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v_ref_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_args_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_del_object(v___x_582_);
v_ref_601_ = lean_ctor_get(v_a_556_, 5);
v___x_602_ = l_Lean_Syntax_getArg(v___x_594_, v___x_593_);
lean_dec(v___x_594_);
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = l_Lean_Syntax_getArg(v_val_580_, v___x_603_);
v_args_605_ = l_Lean_Syntax_getArgs(v___x_602_);
lean_dec(v___x_602_);
v___x_606_ = l_Lean_SourceInfo_fromRef(v_ref_601_, v___x_586_);
v___x_607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11));
v___x_608_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_606_, 11);
v___x_609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14));
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16));
v___x_612_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18));
v___x_613_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20));
v___x_614_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21));
v___x_615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_606_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22);
v___x_617_ = l_Array_append___redArg(v___x_616_, v_args_605_);
lean_dec_ref(v_args_605_);
v___x_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_606_);
lean_ctor_set(v___x_618_, 1, v___x_612_);
lean_ctor_set(v___x_618_, 2, v___x_617_);
v___x_619_ = l_Lean_Syntax_node2(v___x_606_, v___x_613_, v___x_615_, v___x_618_);
v___x_620_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23));
v___x_621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_606_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25));
v___x_624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_606_);
lean_ctor_set(v___x_624_, 1, v___x_622_);
v___x_625_ = l_Lean_Syntax_node2(v___x_606_, v___x_623_, v___x_624_, v___x_604_);
v___x_626_ = l_Lean_Syntax_node3(v___x_606_, v___x_612_, v___x_619_, v___x_621_, v___x_625_);
v___x_627_ = l_Lean_Syntax_node1(v___x_606_, v___x_611_, v___x_626_);
v___x_628_ = l_Lean_Syntax_node1(v___x_606_, v___x_610_, v___x_627_);
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26));
v___x_630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_606_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_Syntax_node3(v___x_606_, v___x_607_, v___x_609_, v___x_628_, v___x_630_);
v___x_632_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_584_, v_mv_551_, v_val_580_, v___x_631_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_val_580_);
v___y_566_ = v___x_632_;
goto v___jp_565_;
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lean_Syntax_getArg(v_val_580_, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28));
v___x_636_ = l_Lean_Syntax_isOfKind(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_639_; 
lean_dec(v_val_580_);
lean_dec(v_mv_551_);
v___x_637_ = lean_box(v___x_636_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
lean_ctor_set(v___x_582_, 0, v___x_637_);
v___x_639_ = v___x_582_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v_ref_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_del_object(v___x_582_);
v_ref_641_ = lean_ctor_get(v_a_556_, 5);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = l_Lean_Syntax_getArg(v_val_580_, v___x_642_);
v___x_644_ = 0;
v___x_645_ = l_Lean_SourceInfo_fromRef(v_ref_641_, v___x_644_);
v___x_646_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_647_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25));
lean_inc(v___x_645_);
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_645_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
v___x_649_ = l_Lean_Syntax_node2(v___x_645_, v___x_647_, v___x_648_, v___x_643_);
v___x_650_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_584_, v_mv_551_, v_val_580_, v___x_649_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_val_580_);
v___y_566_ = v___x_650_;
goto v___jp_565_;
}
}
}
}
else
{
uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v___x_579_);
lean_dec(v_mv_551_);
v___x_652_ = 0;
v___x_653_ = lean_box(v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
v___jp_559_:
{
if (v___y_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v___y_560_);
v___x_562_ = lean_box(v___y_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___y_560_);
return v___x_564_;
}
}
v___jp_565_:
{
if (lean_obj_tag(v___y_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_a_567_ = lean_ctor_get(v___y_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___y_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_569_ = v___y_566_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___y_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_a_571_; lean_object* v___x_573_; 
v_a_571_ = lean_ctor_get(v_a_567_, 0);
lean_inc(v_a_571_);
lean_dec(v_a_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_a_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v_a_576_; uint8_t v___x_577_; 
v_a_576_ = lean_ctor_get(v___y_566_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___y_566_, 1);
v___x_577_ = l_Lean_Exception_isInterrupt(v_a_576_);
if (v___x_577_ == 0)
{
uint8_t v___x_578_; 
lean_inc(v_a_576_);
v___x_578_ = l_Lean_Exception_isRuntime(v_a_576_);
v___y_560_ = v_a_576_;
v___y_561_ = v___x_578_;
goto v___jp_559_;
}
else
{
v___y_560_ = v_a_576_;
v___y_561_ = v___x_577_;
goto v___jp_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_655_, lean_object* v_n_656_, lean_object* v_mv_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_655_, v_n_656_, v_mv_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_n_656_);
lean_dec_ref(v_invariantAlts_655_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_666_, lean_object* v_m_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_667_, v_a_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_670_, lean_object* v_m_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(v_00_u03b2_670_, v_m_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec_ref(v_m_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_674_, v___y_678_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(v_mvarId_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v_mvarId_683_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_692_, lean_object* v_val_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_692_, v_val_693_, v___y_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_702_, lean_object* v_val_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(v_mvarId_702_, v_val_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_712_, lean_object* v_a_713_, lean_object* v_x_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_713_, v_x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_716_, lean_object* v_a_717_, lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_716_, v_a_717_, v_x_718_);
lean_dec(v_x_718_);
lean_dec(v_a_717_);
return v_res_719_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_721_, v_x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_724_, v_x_725_, v_x_726_);
lean_dec(v_x_726_);
lean_dec_ref(v_x_725_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_730_, v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, size_t v_x_736_, lean_object* v_x_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_735_, v_x_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
size_t v_x_18696__boxed_743_; uint8_t v_res_744_; lean_object* v_r_745_; 
v_x_18696__boxed_743_ = lean_unbox_usize(v_x_741_);
lean_dec(v_x_741_);
v_res_744_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_739_, v_x_740_, v_x_18696__boxed_743_, v_x_742_);
lean_dec(v_x_742_);
lean_dec_ref(v_x_740_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, size_t v_x_748_, size_t v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_747_, v_x_748_, v_x_749_, v_x_750_, v_x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
size_t v_x_18707__boxed_759_; size_t v_x_18708__boxed_760_; lean_object* v_res_761_; 
v_x_18707__boxed_759_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_x_18708__boxed_760_ = lean_unbox_usize(v_x_756_);
lean_dec(v_x_756_);
v_res_761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_753_, v_x_754_, v_x_18707__boxed_759_, v_x_18708__boxed_760_, v_x_757_, v_x_758_);
return v_res_761_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_762_, lean_object* v_keys_763_, lean_object* v_vals_764_, lean_object* v_heq_765_, lean_object* v_i_766_, lean_object* v_k_767_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_763_, v_i_766_, v_k_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_769_, lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_heq_772_, lean_object* v_i_773_, lean_object* v_k_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_769_, v_keys_770_, v_vals_771_, v_heq_772_, v_i_773_, v_k_774_);
lean_dec(v_k_774_);
lean_dec_ref(v_vals_771_);
lean_dec_ref(v_keys_770_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_777_, lean_object* v_n_778_, lean_object* v_k_779_, lean_object* v_v_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_778_, v_k_779_, v_v_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_782_, size_t v_depth_783_, lean_object* v_keys_784_, lean_object* v_vals_785_, lean_object* v_heq_786_, lean_object* v_i_787_, lean_object* v_entries_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_783_, v_keys_784_, v_vals_785_, v_i_787_, v_entries_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_790_, lean_object* v_depth_791_, lean_object* v_keys_792_, lean_object* v_vals_793_, lean_object* v_heq_794_, lean_object* v_i_795_, lean_object* v_entries_796_){
_start:
{
size_t v_depth_boxed_797_; lean_object* v_res_798_; 
v_depth_boxed_797_ = lean_unbox_usize(v_depth_791_);
lean_dec(v_depth_791_);
v_res_798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_790_, v_depth_boxed_797_, v_keys_792_, v_vals_793_, v_heq_794_, v_i_795_, v_entries_796_);
lean_dec_ref(v_vals_793_);
lean_dec_ref(v_keys_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_800_, v_x_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_805_, lean_object* v_x_806_){
_start:
{
if (lean_obj_tag(v_x_806_) == 0)
{
uint8_t v___x_807_; 
v___x_807_ = 0;
return v___x_807_;
}
else
{
lean_object* v_key_808_; lean_object* v_tail_809_; uint8_t v___x_810_; 
v_key_808_ = lean_ctor_get(v_x_806_, 0);
v_tail_809_ = lean_ctor_get(v_x_806_, 2);
v___x_810_ = lean_nat_dec_eq(v_key_808_, v_a_805_);
if (v___x_810_ == 0)
{
v_x_806_ = v_tail_809_;
goto _start;
}
else
{
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_812_, lean_object* v_x_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_812_, v_x_813_);
lean_dec(v_x_813_);
lean_dec(v_a_812_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
return v_x_816_;
}
else
{
lean_object* v_key_818_; lean_object* v_value_819_; lean_object* v_tail_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_843_; 
v_key_818_ = lean_ctor_get(v_x_817_, 0);
v_value_819_ = lean_ctor_get(v_x_817_, 1);
v_tail_820_ = lean_ctor_get(v_x_817_, 2);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_817_);
if (v_isSharedCheck_843_ == 0)
{
v___x_822_ = v_x_817_;
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_tail_820_);
lean_inc(v_value_819_);
lean_inc(v_key_818_);
lean_dec(v_x_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_843_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v_fold_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_824_ = lean_array_get_size(v_x_816_);
v___x_825_ = lean_uint64_of_nat(v_key_818_);
v___x_826_ = 32ULL;
v___x_827_ = lean_uint64_shift_right(v___x_825_, v___x_826_);
v_fold_828_ = lean_uint64_xor(v___x_825_, v___x_827_);
v___x_829_ = 16ULL;
v___x_830_ = lean_uint64_shift_right(v_fold_828_, v___x_829_);
v___x_831_ = lean_uint64_xor(v_fold_828_, v___x_830_);
v___x_832_ = lean_uint64_to_usize(v___x_831_);
v___x_833_ = lean_usize_of_nat(v___x_824_);
v___x_834_ = ((size_t)1ULL);
v___x_835_ = lean_usize_sub(v___x_833_, v___x_834_);
v___x_836_ = lean_usize_land(v___x_832_, v___x_835_);
v___x_837_ = lean_array_uget_borrowed(v_x_816_, v___x_836_);
lean_inc(v___x_837_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 2, v___x_837_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_key_818_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_value_819_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v___x_837_);
v___x_839_ = v_reuseFailAlloc_842_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_array_uset(v_x_816_, v___x_836_, v___x_839_);
v_x_816_ = v___x_840_;
v_x_817_ = v_tail_820_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_844_, lean_object* v_source_845_, lean_object* v_target_846_){
_start:
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_array_get_size(v_source_845_);
v___x_848_ = lean_nat_dec_lt(v_i_844_, v___x_847_);
if (v___x_848_ == 0)
{
lean_dec_ref(v_source_845_);
lean_dec(v_i_844_);
return v_target_846_;
}
else
{
lean_object* v_es_849_; lean_object* v___x_850_; lean_object* v_source_851_; lean_object* v_target_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_es_849_ = lean_array_fget(v_source_845_, v_i_844_);
v___x_850_ = lean_box(0);
v_source_851_ = lean_array_fset(v_source_845_, v_i_844_, v___x_850_);
v_target_852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_846_, v_es_849_);
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_i_844_, v___x_853_);
lean_dec(v_i_844_);
v_i_844_ = v___x_854_;
v_source_845_ = v_source_851_;
v_target_846_ = v_target_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_nbuckets_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_857_ = lean_array_get_size(v_data_856_);
v___x_858_ = lean_unsigned_to_nat(2u);
v_nbuckets_859_ = lean_nat_mul(v___x_857_, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_box(0);
v___x_862_ = lean_mk_array(v_nbuckets_859_, v___x_861_);
v___x_863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_860_, v_data_856_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_864_, lean_object* v_a_865_, lean_object* v_b_866_){
_start:
{
lean_object* v_size_867_; lean_object* v_buckets_868_; lean_object* v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v_fold_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v_bkt_882_; uint8_t v___x_883_; 
v_size_867_ = lean_ctor_get(v_m_864_, 0);
v_buckets_868_ = lean_ctor_get(v_m_864_, 1);
v___x_869_ = lean_array_get_size(v_buckets_868_);
v___x_870_ = lean_uint64_of_nat(v_a_865_);
v___x_871_ = 32ULL;
v___x_872_ = lean_uint64_shift_right(v___x_870_, v___x_871_);
v_fold_873_ = lean_uint64_xor(v___x_870_, v___x_872_);
v___x_874_ = 16ULL;
v___x_875_ = lean_uint64_shift_right(v_fold_873_, v___x_874_);
v___x_876_ = lean_uint64_xor(v_fold_873_, v___x_875_);
v___x_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = lean_usize_of_nat(v___x_869_);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_sub(v___x_878_, v___x_879_);
v___x_881_ = lean_usize_land(v___x_877_, v___x_880_);
v_bkt_882_ = lean_array_uget_borrowed(v_buckets_868_, v___x_881_);
v___x_883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_865_, v_bkt_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_904_; 
lean_inc_ref(v_buckets_868_);
lean_inc(v_size_867_);
v_isSharedCheck_904_ = !lean_is_exclusive(v_m_864_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; lean_object* v_unused_906_; 
v_unused_905_ = lean_ctor_get(v_m_864_, 1);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_m_864_, 0);
lean_dec(v_unused_906_);
v___x_885_ = v_m_864_;
v_isShared_886_ = v_isSharedCheck_904_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_m_864_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_904_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v_size_x27_888_; lean_object* v___x_889_; lean_object* v_buckets_x27_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_887_ = lean_unsigned_to_nat(1u);
v_size_x27_888_ = lean_nat_add(v_size_867_, v___x_887_);
lean_dec(v_size_867_);
lean_inc(v_bkt_882_);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v_a_865_);
lean_ctor_set(v___x_889_, 1, v_b_866_);
lean_ctor_set(v___x_889_, 2, v_bkt_882_);
v_buckets_x27_890_ = lean_array_uset(v_buckets_868_, v___x_881_, v___x_889_);
v___x_891_ = lean_unsigned_to_nat(4u);
v___x_892_ = lean_nat_mul(v_size_x27_888_, v___x_891_);
v___x_893_ = lean_unsigned_to_nat(3u);
v___x_894_ = lean_nat_div(v___x_892_, v___x_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_array_get_size(v_buckets_x27_890_);
v___x_896_ = lean_nat_dec_le(v___x_894_, v___x_895_);
lean_dec(v___x_894_);
if (v___x_896_ == 0)
{
lean_object* v_val_897_; lean_object* v___x_899_; 
v_val_897_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_890_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v_val_897_);
lean_ctor_set(v___x_885_, 0, v_size_x27_888_);
v___x_899_ = v___x_885_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_size_x27_888_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_val_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
else
{
lean_object* v___x_902_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v_buckets_x27_890_);
lean_ctor_set(v___x_885_, 0, v_size_x27_888_);
v___x_902_ = v___x_885_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_size_x27_888_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_buckets_x27_890_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_dec(v_b_866_);
lean_dec(v_a_865_);
return v_m_864_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_907_, lean_object* v_as_x27_908_, lean_object* v_b_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
if (lean_obj_tag(v_as_x27_908_) == 0)
{
lean_object* v___x_919_; 
lean_dec_ref(v___x_907_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v_b_909_);
return v___x_919_;
}
else
{
lean_object* v_head_920_; lean_object* v_tail_921_; lean_object* v___x_922_; 
v_head_920_ = lean_ctor_get(v_as_x27_908_, 0);
v_tail_921_ = lean_ctor_get(v_as_x27_908_, 1);
lean_inc(v_head_920_);
v___x_922_ = l_Lean_MVarId_getType(v_head_920_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; uint8_t v___x_924_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
lean_inc_ref(v___x_907_);
v___x_924_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_907_, v_a_923_);
lean_dec(v_a_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
lean_inc(v_head_920_);
v___x_925_ = lean_array_push(v_b_909_, v_head_920_);
v_as_x27_908_ = v_tail_921_;
v_b_909_ = v___x_925_;
goto _start;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_specBackwardRuleCache_929_; lean_object* v_splitBackwardRuleCache_930_; lean_object* v_latticeBackwardRuleCache_931_; lean_object* v_invariants_932_; lean_object* v_vcs_933_; lean_object* v_simpState_934_; lean_object* v_fuel_935_; lean_object* v_inlineHandledInvariants_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_992_; 
v___x_927_ = lean_st_ref_get(v___y_911_);
v___x_928_ = lean_st_ref_take(v___y_911_);
v_specBackwardRuleCache_929_ = lean_ctor_get(v___x_928_, 0);
v_splitBackwardRuleCache_930_ = lean_ctor_get(v___x_928_, 1);
v_latticeBackwardRuleCache_931_ = lean_ctor_get(v___x_928_, 2);
v_invariants_932_ = lean_ctor_get(v___x_928_, 3);
v_vcs_933_ = lean_ctor_get(v___x_928_, 4);
v_simpState_934_ = lean_ctor_get(v___x_928_, 5);
v_fuel_935_ = lean_ctor_get(v___x_928_, 6);
v_inlineHandledInvariants_936_ = lean_ctor_get(v___x_928_, 7);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_992_ == 0)
{
v___x_938_ = v___x_928_;
v_isShared_939_ = v_isSharedCheck_992_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_inlineHandledInvariants_936_);
lean_inc(v_fuel_935_);
lean_inc(v_simpState_934_);
lean_inc(v_vcs_933_);
lean_inc(v_invariants_932_);
lean_inc(v_latticeBackwardRuleCache_931_);
lean_inc(v_splitBackwardRuleCache_930_);
lean_inc(v_specBackwardRuleCache_929_);
lean_dec(v___x_928_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_992_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
lean_inc(v_head_920_);
v___x_940_ = lean_array_push(v_invariants_932_, v_head_920_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 3, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_specBackwardRuleCache_929_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_splitBackwardRuleCache_930_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_latticeBackwardRuleCache_931_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_vcs_933_);
lean_ctor_set(v_reuseFailAlloc_991_, 5, v_simpState_934_);
lean_ctor_set(v_reuseFailAlloc_991_, 6, v_fuel_935_);
lean_ctor_set(v_reuseFailAlloc_991_, 7, v_inlineHandledInvariants_936_);
v___x_942_ = v_reuseFailAlloc_991_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v_invariants_944_; lean_object* v_invariantAlts_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_943_ = lean_st_ref_set(v___y_911_, v___x_942_);
v_invariants_944_ = lean_ctor_get(v___x_927_, 3);
lean_inc_ref(v_invariants_944_);
lean_dec(v___x_927_);
v_invariantAlts_945_ = lean_ctor_get(v___y_910_, 2);
v___x_946_ = lean_array_get_size(v_invariants_944_);
lean_dec_ref(v_invariants_944_);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_add(v___x_946_, v___x_947_);
lean_inc(v_head_920_);
v___x_949_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_945_, v___x_948_, v_head_920_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; uint8_t v___x_951_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = lean_unbox(v_a_950_);
lean_dec(v_a_950_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; lean_object* v___x_953_; 
lean_dec(v___x_948_);
v___x_952_ = 2;
lean_inc(v_head_920_);
v___x_953_ = l_Lean_MVarId_setKind___redArg(v_head_920_, v___x_952_, v___y_915_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec_ref_known(v___x_953_, 1);
v_as_x27_908_ = v_tail_921_;
goto _start;
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec_ref(v_b_909_);
lean_dec_ref(v___x_907_);
v_a_955_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_953_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_963_; lean_object* v_specBackwardRuleCache_964_; lean_object* v_splitBackwardRuleCache_965_; lean_object* v_latticeBackwardRuleCache_966_; lean_object* v_invariants_967_; lean_object* v_vcs_968_; lean_object* v_simpState_969_; lean_object* v_fuel_970_; lean_object* v_inlineHandledInvariants_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_982_; 
v___x_963_ = lean_st_ref_take(v___y_911_);
v_specBackwardRuleCache_964_ = lean_ctor_get(v___x_963_, 0);
v_splitBackwardRuleCache_965_ = lean_ctor_get(v___x_963_, 1);
v_latticeBackwardRuleCache_966_ = lean_ctor_get(v___x_963_, 2);
v_invariants_967_ = lean_ctor_get(v___x_963_, 3);
v_vcs_968_ = lean_ctor_get(v___x_963_, 4);
v_simpState_969_ = lean_ctor_get(v___x_963_, 5);
v_fuel_970_ = lean_ctor_get(v___x_963_, 6);
v_inlineHandledInvariants_971_ = lean_ctor_get(v___x_963_, 7);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_982_ == 0)
{
v___x_973_ = v___x_963_;
v_isShared_974_ = v_isSharedCheck_982_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_inlineHandledInvariants_971_);
lean_inc(v_fuel_970_);
lean_inc(v_simpState_969_);
lean_inc(v_vcs_968_);
lean_inc(v_invariants_967_);
lean_inc(v_latticeBackwardRuleCache_966_);
lean_inc(v_splitBackwardRuleCache_965_);
lean_inc(v_specBackwardRuleCache_964_);
lean_dec(v___x_963_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_982_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_975_ = lean_box(0);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_971_, v___x_948_, v___x_975_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 7, v___x_976_);
v___x_978_ = v___x_973_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_specBackwardRuleCache_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_splitBackwardRuleCache_965_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_latticeBackwardRuleCache_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_invariants_967_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_vcs_968_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_simpState_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_fuel_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v___x_976_);
v___x_978_ = v_reuseFailAlloc_981_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_st_ref_set(v___y_911_, v___x_978_);
v_as_x27_908_ = v_tail_921_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v___x_948_);
lean_dec_ref(v_b_909_);
lean_dec_ref(v___x_907_);
v_a_983_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_949_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_949_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_b_909_);
lean_dec_ref(v___x_907_);
v_a_993_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_922_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_922_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_1001_, lean_object* v_as_x27_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1001_, v_as_x27_1002_, v_b_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v_as_x27_1002_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v_env_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = lean_st_ref_get(v_a_1027_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref(v_env_1030_);
lean_dec(v___x_1029_);
v___x_1031_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1032_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_1030_, v_subgoals_1016_, v___x_1031_, v_a_1017_, v_a_1018_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_subgoals_1033_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1047_, lean_object* v_m_1048_, lean_object* v_a_1049_, lean_object* v_b_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1048_, v_a_1049_, v_b_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1052_, lean_object* v_as_1053_, lean_object* v_as_x27_1054_, lean_object* v_b_1055_, lean_object* v_a_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1052_, v_as_x27_1054_, v_b_1055_, v___y_1057_, v___y_1058_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1070_ = _args[0];
lean_object* v_as_1071_ = _args[1];
lean_object* v_as_x27_1072_ = _args[2];
lean_object* v_b_1073_ = _args[3];
lean_object* v_a_1074_ = _args[4];
lean_object* v___y_1075_ = _args[5];
lean_object* v___y_1076_ = _args[6];
lean_object* v___y_1077_ = _args[7];
lean_object* v___y_1078_ = _args[8];
lean_object* v___y_1079_ = _args[9];
lean_object* v___y_1080_ = _args[10];
lean_object* v___y_1081_ = _args[11];
lean_object* v___y_1082_ = _args[12];
lean_object* v___y_1083_ = _args[13];
lean_object* v___y_1084_ = _args[14];
lean_object* v___y_1085_ = _args[15];
lean_object* v___y_1086_ = _args[16];
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(v___x_1070_, v_as_1071_, v_as_x27_1072_, v_b_1073_, v_a_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_as_x27_1072_);
lean_dec(v_as_1071_);
return v_res_1087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1088_, lean_object* v_a_1089_, lean_object* v_x_1090_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1089_, v_x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1092_, lean_object* v_a_1093_, lean_object* v_x_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1092_, v_a_1093_, v_x_1094_);
lean_dec(v_x_1094_);
lean_dec(v_a_1093_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1097_, lean_object* v_data_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1100_, lean_object* v_i_1101_, lean_object* v_source_1102_, lean_object* v_target_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1101_, v_source_1102_, v_target_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1106_, v_x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object* v_goal_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_toGoalState_1122_; lean_object* v_mvarId_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1221_; 
v_toGoalState_1122_ = lean_ctor_get(v_goal_1109_, 0);
v_mvarId_1123_ = lean_ctor_get(v_goal_1109_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_goal_1109_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1125_ = v_goal_1109_;
v_isShared_1126_ = v_isSharedCheck_1221_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_mvarId_1123_);
lean_inc(v_toGoalState_1122_);
lean_dec(v_goal_1109_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1221_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(v_mvarId_1123_, v_a_1110_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_a_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_toGoalState_1122_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_a_1128_);
v___x_1130_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v___x_1130_, v_a_1110_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1203_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1203_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1203_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_toGoalState_1136_; lean_object* v_mvarId_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1202_; 
v_toGoalState_1136_ = lean_ctor_get(v_a_1132_, 0);
v_mvarId_1137_ = lean_ctor_get(v_a_1132_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_a_1132_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1139_ = v_a_1132_;
v_isShared_1140_ = v_isSharedCheck_1202_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_mvarId_1137_);
lean_inc(v_toGoalState_1136_);
lean_dec(v_a_1132_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1202_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_mvarId_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; uint8_t v_inconsistent_1177_; 
v_inconsistent_1177_ = lean_ctor_get_uint8(v_toGoalState_1136_, sizeof(void*)*17);
if (v_inconsistent_1177_ == 0)
{
uint8_t v_trivial_1178_; 
lean_del_object(v___x_1134_);
v_trivial_1178_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*4);
if (v_trivial_1178_ == 0)
{
v_mvarId_1142_ = v_mvarId_1137_;
v___y_1143_ = v_a_1111_;
v___y_1144_ = v_a_1118_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_mvarId_1137_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_val_1184_; 
lean_del_object(v___x_1182_);
v_val_1184_ = lean_ctor_get(v_a_1180_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v_a_1180_, 1);
v_mvarId_1142_ = v_val_1184_;
v___y_1143_ = v_a_1111_;
v___y_1144_ = v_a_1118_;
goto v___jp_1141_;
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_dec(v_a_1180_);
lean_del_object(v___x_1139_);
lean_dec_ref(v_toGoalState_1136_);
v___x_1185_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1185_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_del_object(v___x_1139_);
lean_dec_ref(v_toGoalState_1136_);
v_a_1190_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1179_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1179_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
lean_del_object(v___x_1139_);
lean_dec(v_mvarId_1137_);
lean_dec_ref(v_toGoalState_1136_);
v___x_1198_ = lean_box(0);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1198_);
v___x_1200_ = v___x_1134_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
v___jp_1141_:
{
uint8_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = 2;
lean_inc(v_mvarId_1142_);
v___x_1146_ = l_Lean_MVarId_setKind___redArg(v_mvarId_1142_, v___x_1145_, v___y_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1175_; 
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1176_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1175_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1175_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v_specBackwardRuleCache_1151_; lean_object* v_splitBackwardRuleCache_1152_; lean_object* v_latticeBackwardRuleCache_1153_; lean_object* v_invariants_1154_; lean_object* v_vcs_1155_; lean_object* v_simpState_1156_; lean_object* v_fuel_1157_; lean_object* v_inlineHandledInvariants_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1174_; 
v___x_1150_ = lean_st_ref_take(v___y_1143_);
v_specBackwardRuleCache_1151_ = lean_ctor_get(v___x_1150_, 0);
v_splitBackwardRuleCache_1152_ = lean_ctor_get(v___x_1150_, 1);
v_latticeBackwardRuleCache_1153_ = lean_ctor_get(v___x_1150_, 2);
v_invariants_1154_ = lean_ctor_get(v___x_1150_, 3);
v_vcs_1155_ = lean_ctor_get(v___x_1150_, 4);
v_simpState_1156_ = lean_ctor_get(v___x_1150_, 5);
v_fuel_1157_ = lean_ctor_get(v___x_1150_, 6);
v_inlineHandledInvariants_1158_ = lean_ctor_get(v___x_1150_, 7);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1160_ = v___x_1150_;
v_isShared_1161_ = v_isSharedCheck_1174_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_inlineHandledInvariants_1158_);
lean_inc(v_fuel_1157_);
lean_inc(v_simpState_1156_);
lean_inc(v_vcs_1155_);
lean_inc(v_invariants_1154_);
lean_inc(v_latticeBackwardRuleCache_1153_);
lean_inc(v_splitBackwardRuleCache_1152_);
lean_inc(v_specBackwardRuleCache_1151_);
lean_dec(v___x_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1174_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_mvarId_1142_);
v___x_1163_ = v___x_1139_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_toGoalState_1136_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_mvarId_1142_);
v___x_1163_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_array_push(v_vcs_1155_, v___x_1163_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v___x_1164_);
v___x_1166_ = v___x_1160_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_specBackwardRuleCache_1151_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_splitBackwardRuleCache_1152_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_latticeBackwardRuleCache_1153_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_invariants_1154_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1172_, 5, v_simpState_1156_);
lean_ctor_set(v_reuseFailAlloc_1172_, 6, v_fuel_1157_);
lean_ctor_set(v_reuseFailAlloc_1172_, 7, v_inlineHandledInvariants_1158_);
v___x_1166_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = lean_st_ref_set(v___y_1143_, v___x_1166_);
v___x_1168_ = lean_box(0);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1168_);
v___x_1170_ = v___x_1148_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
else
{
lean_dec(v_mvarId_1142_);
lean_del_object(v___x_1139_);
lean_dec_ref(v_toGoalState_1136_);
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
v_a_1204_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1131_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1131_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1125_);
lean_dec_ref(v_toGoalState_1122_);
v_a_1213_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1127_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1127_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object* v_goal_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object* v_goal_1236_, lean_object* v_scope_1237_, size_t v_sz_1238_, size_t v_i_1239_, lean_object* v_bs_1240_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
if (v___x_1241_ == 0)
{
lean_dec_ref(v_scope_1237_);
return v_bs_1240_;
}
else
{
lean_object* v_toGoalState_1242_; lean_object* v_v_1243_; lean_object* v___x_1244_; lean_object* v_bs_x27_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v_toGoalState_1242_ = lean_ctor_get(v_goal_1236_, 0);
v_v_1243_ = lean_array_uget(v_bs_1240_, v_i_1239_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v_bs_x27_1245_ = lean_array_uset(v_bs_1240_, v_i_1239_, v___x_1244_);
lean_inc_ref(v_toGoalState_1242_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_toGoalState_1242_);
lean_ctor_set(v___x_1246_, 1, v_v_1243_);
lean_inc_ref(v_scope_1237_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v_scope_1237_);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_i_1239_, v___x_1248_);
v___x_1250_ = lean_array_uset(v_bs_x27_1245_, v_i_1239_, v___x_1247_);
v_i_1239_ = v___x_1249_;
v_bs_1240_ = v___x_1250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object* v_goal_1252_, lean_object* v_scope_1253_, lean_object* v_sz_1254_, lean_object* v_i_1255_, lean_object* v_bs_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1254_);
lean_dec(v_sz_1254_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1255_);
lean_dec(v_i_1255_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_goal_1252_, v_scope_1253_, v_sz_boxed_1257_, v_i_boxed_1258_, v_bs_1256_);
lean_dec_ref(v_goal_1252_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(lean_object* v_a_1260_, lean_object* v_scope_1261_, lean_object* v___x_1262_, lean_object* v_goal_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1276_ = l_Array_reverse___redArg(v_a_1260_);
v_sz_1277_ = lean_array_size(v___x_1276_);
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_goal_1263_, v_scope_1261_, v_sz_1277_, v___x_1278_, v___x_1276_);
v___x_1280_ = l_Array_append___redArg(v___x_1262_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0___boxed(lean_object* v_a_1283_, lean_object* v_scope_1284_, lean_object* v___x_1285_, lean_object* v_goal_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1283_, v_scope_1284_, v___x_1285_, v_goal_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_goal_1286_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(lean_object* v_a_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___y_1314_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1334_ = lean_array_get_size(v_a_1300_);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_sub(v___x_1334_, v___x_1335_);
v___x_1337_ = lean_nat_dec_lt(v___x_1336_, v___x_1334_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_dec(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1300_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; lean_object* v_goal_1340_; lean_object* v_toGoalState_1341_; lean_object* v_scope_1342_; lean_object* v_mvarId_1343_; uint8_t v_inconsistent_1344_; lean_object* v___x_1345_; 
v___x_1339_ = lean_array_fget_borrowed(v_a_1300_, v___x_1336_);
lean_dec(v___x_1336_);
v_goal_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_goal_1340_);
v_toGoalState_1341_ = lean_ctor_get(v_goal_1340_, 0);
v_scope_1342_ = lean_ctor_get(v___x_1339_, 1);
lean_inc_ref(v_scope_1342_);
v_mvarId_1343_ = lean_ctor_get(v_goal_1340_, 1);
v_inconsistent_1344_ = lean_ctor_get_uint8(v_toGoalState_1341_, sizeof(void*)*17);
v___x_1345_ = lean_array_pop(v_a_1300_);
if (v_inconsistent_1344_ == 0)
{
lean_object* v___x_1346_; 
lean_inc(v_mvarId_1343_);
v___x_1346_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_1342_, v_mvarId_1343_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v_scope_1348_; lean_object* v_subgoals_1349_; lean_object* v___x_1350_; 
v_scope_1348_ = lean_ctor_get(v_a_1347_, 0);
lean_inc_ref(v_scope_1348_);
v_subgoals_1349_ = lean_ctor_get(v_a_1347_, 1);
lean_inc(v_subgoals_1349_);
lean_dec_ref_known(v_a_1347_, 2);
v___x_1350_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1349_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v_subgoals_1349_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = lean_array_get_size(v_a_1351_);
v___x_1353_ = lean_nat_dec_lt(v___x_1335_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1351_, v_scope_1348_, v___x_1345_, v_goal_1340_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec_ref(v_goal_1340_);
v___y_1314_ = v___x_1354_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_1340_, v___y_1301_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1351_, v_scope_1348_, v___x_1345_, v_a_1356_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v_a_1356_);
v___y_1314_ = v___x_1357_;
goto v___jp_1313_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_a_1351_);
lean_dec_ref(v_scope_1348_);
lean_dec_ref(v___x_1345_);
v_a_1358_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1355_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1355_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v_scope_1348_);
lean_dec_ref(v___x_1345_);
lean_dec_ref(v_goal_1340_);
v_a_1366_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1350_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1350_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
else
{
lean_object* v___x_1374_; 
lean_dec_ref_known(v_a_1347_, 1);
v___x_1374_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1340_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_dec_ref_known(v___x_1374_, 1);
v_a_1300_ = v___x_1345_;
goto _start;
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v___x_1345_);
v_a_1376_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1374_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1374_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v___x_1345_);
lean_dec_ref(v_goal_1340_);
v_a_1384_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1346_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1346_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1342_);
lean_dec_ref(v_goal_1340_);
v_a_1300_ = v___x_1345_;
goto _start;
}
}
v___jp_1313_:
{
if (lean_obj_tag(v___y_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1325_; 
v_a_1315_ = lean_ctor_get(v___y_1314_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___y_1314_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1317_ = v___y_1314_;
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___y_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1325_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
if (lean_obj_tag(v_a_1315_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v_a_1315_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v_a_1315_, 1);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_a_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
else
{
lean_object* v_a_1323_; 
lean_del_object(v___x_1317_);
v_a_1323_ = lean_ctor_get(v_a_1315_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v_a_1315_, 1);
v_a_1300_ = v_a_1323_;
goto _start;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___y_1314_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___y_1314_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___y_1314_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___y_1314_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___boxed(lean_object* v_a_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object* v_scope_1407_, lean_object* v_goal_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_toGoalState_1421_; lean_object* v_mvarId_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1461_; 
v_toGoalState_1421_ = lean_ctor_get(v_goal_1408_, 0);
v_mvarId_1422_ = lean_ctor_get(v_goal_1408_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_goal_1408_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1424_ = v_goal_1408_;
v_isShared_1425_ = v_isSharedCheck_1461_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_mvarId_1422_);
lean_inc(v_toGoalState_1421_);
lean_dec(v_goal_1408_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1461_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1422_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v_a_1427_);
v___x_1429_ = v___x_1424_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_toGoalState_1421_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1427_);
v___x_1429_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v_scope_1407_);
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1431_);
v___x_1433_ = lean_array_push(v___x_1432_, v___x_1430_);
v___x_1434_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v___x_1433_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1442_; 
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v___x_1434_, 0);
lean_dec(v_unused_1443_);
v___x_1436_ = v___x_1434_;
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
else
{
lean_dec(v___x_1434_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1442_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_box(0);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1438_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_a_1444_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1434_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1434_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_del_object(v___x_1424_);
lean_dec_ref(v_toGoalState_1421_);
lean_dec_ref(v_scope_1407_);
v_a_1453_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1426_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1426_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object* v_scope_1462_, lean_object* v_goal_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_1462_, v_goal_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(lean_object* v_inst_1477_, lean_object* v_a_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v_a_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object* v_inst_1492_, lean_object* v_a_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_inst_1492_, v_a_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(lean_object* v_as_1508_, lean_object* v_i_1509_, lean_object* v_j_1510_, lean_object* v_bs_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_zero_1517_; uint8_t v_isZero_1518_; 
v_zero_1517_ = lean_unsigned_to_nat(0u);
v_isZero_1518_ = lean_nat_dec_eq(v_i_1509_, v_zero_1517_);
if (v_isZero_1518_ == 1)
{
lean_object* v___x_1519_; 
lean_dec(v_j_1510_);
lean_dec(v_i_1509_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_bs_1511_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; lean_object* v_mvarId_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_array_fget_borrowed(v_as_1508_, v_j_1510_);
v_mvarId_1521_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_mvarId_1521_);
v___x_1522_ = l_Lean_MVarId_getTag(v_mvarId_1521_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0));
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_nat_add(v_j_1510_, v___x_1525_);
lean_dec(v_j_1510_);
lean_inc(v___x_1526_);
v___x_1527_ = l_Nat_reprFast(v___x_1526_);
v___x_1528_ = lean_string_append(v___x_1524_, v___x_1527_);
lean_dec_ref(v___x_1527_);
v___x_1529_ = lean_box(0);
v___x_1530_ = l_Lean_Name_str___override(v___x_1529_, v___x_1528_);
v___x_1531_ = lean_erase_macro_scopes(v_a_1523_);
v___x_1532_ = l_Lean_Name_append(v___x_1530_, v___x_1531_);
lean_inc(v_mvarId_1521_);
v___x_1533_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1521_, v___x_1532_, v___y_1513_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v_n_1535_; lean_object* v___x_1536_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v_n_1535_ = lean_nat_sub(v_i_1509_, v___x_1525_);
lean_dec(v_i_1509_);
v___x_1536_ = lean_array_push(v_bs_1511_, v_a_1534_);
v_i_1509_ = v_n_1535_;
v_j_1510_ = v___x_1526_;
v_bs_1511_ = v___x_1536_;
goto _start;
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v___x_1526_);
lean_dec_ref(v_bs_1511_);
lean_dec(v_i_1509_);
v_a_1538_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1533_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1533_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v_bs_1511_);
lean_dec(v_j_1510_);
lean_dec(v_i_1509_);
v_a_1546_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1522_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1522_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(lean_object* v_as_1554_, lean_object* v_i_1555_, lean_object* v_j_1556_, lean_object* v_bs_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_as_1554_, v_i_1555_, v_j_1556_, v_bs_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec_ref(v_as_1554_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(lean_object* v_as_1565_, lean_object* v_i_1566_, lean_object* v_j_1567_, lean_object* v_bs_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_zero_1571_; uint8_t v_isZero_1572_; 
v_zero_1571_ = lean_unsigned_to_nat(0u);
v_isZero_1572_ = lean_nat_dec_eq(v_i_1566_, v_zero_1571_);
if (v_isZero_1572_ == 1)
{
lean_object* v___x_1573_; 
lean_dec(v_j_1567_);
lean_dec(v_i_1566_);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_bs_1568_);
return v___x_1573_;
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1574_ = lean_array_fget_borrowed(v_as_1565_, v_j_1567_);
v___x_1575_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0));
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_add(v_j_1567_, v___x_1576_);
lean_dec(v_j_1567_);
lean_inc(v___x_1577_);
v___x_1578_ = l_Nat_reprFast(v___x_1577_);
v___x_1579_ = lean_string_append(v___x_1575_, v___x_1578_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Lean_Name_str___override(v___x_1580_, v___x_1579_);
lean_inc(v___x_1574_);
v___x_1582_ = l_Lean_MVarId_setTag___redArg(v___x_1574_, v___x_1581_, v___y_1569_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v_n_1584_; lean_object* v___x_1585_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_n_1584_ = lean_nat_sub(v_i_1566_, v___x_1576_);
lean_dec(v_i_1566_);
v___x_1585_ = lean_array_push(v_bs_1568_, v_a_1583_);
v_i_1566_ = v_n_1584_;
v_j_1567_ = v___x_1577_;
v_bs_1568_ = v___x_1585_;
goto _start;
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v___x_1577_);
lean_dec_ref(v_bs_1568_);
lean_dec(v_i_1566_);
v_a_1587_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1582_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1582_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(lean_object* v_as_1595_, lean_object* v_i_1596_, lean_object* v_j_1597_, lean_object* v_bs_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_as_1595_, v_i_1596_, v_j_1597_, v_bs_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v_as_1595_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v_mctx_1606_; lean_object* v_eAssignment_1607_; uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_st_ref_get(v___y_1603_);
v_mctx_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_ref(v_mctx_1606_);
lean_dec(v___x_1605_);
v_eAssignment_1607_ = lean_ctor_get(v_mctx_1606_, 8);
lean_inc_ref(v_eAssignment_1607_);
lean_dec_ref(v_mctx_1606_);
v___x_1608_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1607_, v_mvarId_1602_);
lean_dec_ref(v_eAssignment_1607_);
v___x_1609_ = lean_box(v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec(v_mvarId_1611_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object* v_as_1615_, size_t v_i_1616_, size_t v_stop_1617_, lean_object* v_b_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_a_1630_; uint8_t v___x_1634_; 
v___x_1634_ = lean_usize_dec_eq(v_i_1616_, v_stop_1617_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v_mvarId_1638_; lean_object* v___x_1639_; 
v___x_1635_ = lean_array_uget_borrowed(v_as_1615_, v_i_1616_);
v_mvarId_1638_ = lean_ctor_get(v___x_1635_, 1);
v___x_1639_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1638_, v___y_1625_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; uint8_t v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = lean_unbox(v_a_1640_);
lean_dec(v_a_1640_);
if (v___x_1641_ == 0)
{
goto v___jp_1636_;
}
else
{
v_a_1630_ = v_b_1618_;
goto v___jp_1629_;
}
}
else
{
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1642_; uint8_t v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1643_ = lean_unbox(v_a_1642_);
lean_dec(v_a_1642_);
if (v___x_1643_ == 0)
{
v_a_1630_ = v_b_1618_;
goto v___jp_1629_;
}
else
{
goto v___jp_1636_;
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v_b_1618_);
v_a_1644_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1639_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1639_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
v___jp_1636_:
{
lean_object* v___x_1637_; 
lean_inc(v___x_1635_);
v___x_1637_ = lean_array_push(v_b_1618_, v___x_1635_);
v_a_1630_ = v___x_1637_;
goto v___jp_1629_;
}
}
else
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_b_1618_);
return v___x_1652_;
}
v___jp_1629_:
{
size_t v___x_1631_; size_t v___x_1632_; 
v___x_1631_ = ((size_t)1ULL);
v___x_1632_ = lean_usize_add(v_i_1616_, v___x_1631_);
v_i_1616_ = v___x_1632_;
v_b_1618_ = v_a_1630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object* v_as_1653_, lean_object* v_i_1654_, lean_object* v_stop_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
size_t v_i_boxed_1667_; size_t v_stop_boxed_1668_; lean_object* v_res_1669_; 
v_i_boxed_1667_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_stop_boxed_1668_ = lean_unbox_usize(v_stop_1655_);
lean_dec(v_stop_1655_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_as_1653_, v_i_boxed_1667_, v_stop_boxed_1668_, v_b_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v_as_1653_);
return v_res_1669_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_unsigned_to_nat(16u);
v___x_1672_ = lean_mk_array(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v___x_1673_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3);
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1679_);
lean_ctor_set(v___x_1681_, 2, v___x_1679_);
lean_ctor_set(v___x_1681_, 3, v___x_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object* v_goal_1682_, lean_object* v_ctx_1683_, lean_object* v_scope_1684_, lean_object* v_stepLimit_x3f_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v_a_1699_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___y_1720_; 
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1);
v___x_1717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1718_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1685_) == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_box(1);
v___y_1720_ = v___x_1766_;
goto v___jp_1719_;
}
else
{
lean_object* v_val_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_val_1767_ = lean_ctor_get(v_stepLimit_x3f_1685_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_stepLimit_x3f_1685_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v_stepLimit_x3f_1685_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_val_1767_);
lean_dec(v_stepLimit_x3f_1685_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 0);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_val_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v___y_1720_ = v___x_1772_;
goto v___jp_1719_;
}
}
}
v___jp_1696_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1698_);
lean_ctor_set(v___x_1700_, 1, v_a_1699_);
lean_ctor_set(v___x_1700_, 2, v___y_1697_);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
return v___x_1701_;
}
v___jp_1702_:
{
if (lean_obj_tag(v___y_1705_) == 0)
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___y_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___y_1705_, 1);
v___y_1697_ = v___y_1703_;
v___y_1698_ = v___y_1704_;
v_a_1699_ = v_a_1706_;
goto v___jp_1696_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref(v___y_1704_);
lean_dec_ref(v___y_1703_);
v_a_1707_ = lean_ctor_get(v___y_1705_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___y_1705_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___y_1705_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___y_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
v___jp_1719_:
{
lean_object* v_initState_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_initState_1721_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_initState_1721_, 0, v___x_1716_);
lean_ctor_set(v_initState_1721_, 1, v___x_1716_);
lean_ctor_set(v_initState_1721_, 2, v___x_1716_);
lean_ctor_set(v_initState_1721_, 3, v___x_1717_);
lean_ctor_set(v_initState_1721_, 4, v___x_1717_);
lean_ctor_set(v_initState_1721_, 5, v___x_1718_);
lean_ctor_set(v_initState_1721_, 6, v___y_1720_);
lean_ctor_set(v_initState_1721_, 7, v___x_1716_);
v___x_1722_ = lean_st_mk_ref(v_initState_1721_);
v___x_1723_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_1684_, v_goal_1682_, v_ctx_1683_, v___x_1722_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; lean_object* v_invariants_1725_; lean_object* v_vcs_1726_; lean_object* v_inlineHandledInvariants_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1724_ = lean_st_ref_get(v___x_1722_);
lean_dec(v___x_1722_);
v_invariants_1725_ = lean_ctor_get(v___x_1724_, 3);
lean_inc_ref(v_invariants_1725_);
v_vcs_1726_ = lean_ctor_get(v___x_1724_, 4);
lean_inc_ref(v_vcs_1726_);
v_inlineHandledInvariants_1727_ = lean_ctor_get(v___x_1724_, 7);
lean_inc_ref(v_inlineHandledInvariants_1727_);
lean_dec(v___x_1724_);
v___x_1728_ = lean_array_get_size(v_invariants_1725_);
v___x_1729_ = lean_mk_empty_array_with_capacity(v___x_1728_);
v___x_1730_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_invariants_1725_, v___x_1728_, v___x_1715_, v___x_1729_, v_a_1692_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec_ref_known(v___x_1730_, 1);
v___x_1731_ = lean_array_get_size(v_vcs_1726_);
v___x_1732_ = lean_mk_empty_array_with_capacity(v___x_1731_);
v___x_1733_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_vcs_1726_, v___x_1731_, v___x_1715_, v___x_1732_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1733_) == 0)
{
uint8_t v___x_1734_; 
lean_dec_ref_known(v___x_1733_, 1);
v___x_1734_ = lean_nat_dec_lt(v___x_1715_, v___x_1731_);
if (v___x_1734_ == 0)
{
lean_dec_ref(v_vcs_1726_);
v___y_1697_ = v_inlineHandledInvariants_1727_;
v___y_1698_ = v_invariants_1725_;
v_a_1699_ = v___x_1717_;
goto v___jp_1696_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_le(v___x_1731_, v___x_1731_);
if (v___x_1735_ == 0)
{
if (v___x_1734_ == 0)
{
lean_dec_ref(v_vcs_1726_);
v___y_1697_ = v_inlineHandledInvariants_1727_;
v___y_1698_ = v_invariants_1725_;
v_a_1699_ = v___x_1717_;
goto v___jp_1696_;
}
else
{
size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = ((size_t)0ULL);
v___x_1737_ = lean_usize_of_nat(v___x_1731_);
v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_vcs_1726_, v___x_1736_, v___x_1737_, v___x_1717_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec_ref(v_vcs_1726_);
v___y_1703_ = v_inlineHandledInvariants_1727_;
v___y_1704_ = v_invariants_1725_;
v___y_1705_ = v___x_1738_;
goto v___jp_1702_;
}
}
else
{
size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = ((size_t)0ULL);
v___x_1740_ = lean_usize_of_nat(v___x_1731_);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_vcs_1726_, v___x_1739_, v___x_1740_, v___x_1717_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec_ref(v_vcs_1726_);
v___y_1703_ = v_inlineHandledInvariants_1727_;
v___y_1704_ = v_invariants_1725_;
v___y_1705_ = v___x_1741_;
goto v___jp_1702_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_inlineHandledInvariants_1727_);
lean_dec_ref(v_vcs_1726_);
lean_dec_ref(v_invariants_1725_);
v_a_1742_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1733_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1733_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_inlineHandledInvariants_1727_);
lean_dec_ref(v_vcs_1726_);
lean_dec_ref(v_invariants_1725_);
v_a_1750_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1730_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1730_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v___x_1722_);
v_a_1758_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1723_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1723_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object* v_goal_1775_, lean_object* v_ctx_1776_, lean_object* v_scope_1777_, lean_object* v_stepLimit_x3f_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_goal_1775_, v_ctx_1776_, v_scope_1777_, v_stepLimit_x3f_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_ctx_1776_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object* v_mvarId_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1790_, v___y_1797_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(v_mvarId_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec(v_mvarId_1802_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object* v_as_1814_, lean_object* v_i_1815_, lean_object* v_j_1816_, lean_object* v_inv_1817_, lean_object* v_bs_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_as_1814_, v_i_1815_, v_j_1816_, v_bs_1818_, v___y_1825_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object* v_as_1830_, lean_object* v_i_1831_, lean_object* v_j_1832_, lean_object* v_inv_1833_, lean_object* v_bs_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(v_as_1830_, v_i_1831_, v_j_1832_, v_inv_1833_, v_bs_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v_as_1830_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object* v_as_1846_, lean_object* v_i_1847_, lean_object* v_j_1848_, lean_object* v_inv_1849_, lean_object* v_bs_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_as_1846_, v_i_1847_, v_j_1848_, v_bs_1850_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_j_1864_, lean_object* v_inv_1865_, lean_object* v_bs_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(v_as_1862_, v_i_1863_, v_j_1864_, v_inv_1865_, v_bs_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v_as_1862_);
return v_res_1877_;
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
