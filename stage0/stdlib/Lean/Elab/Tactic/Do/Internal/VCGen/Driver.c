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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_16492__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_16492__boxed_72_ = lean_unbox_usize(v_x_70_);
lean_dec(v_x_70_);
v_res_73_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_69_, v_x_16492__boxed_72_, v_x_71_);
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
size_t v_x_16635__boxed_238_; size_t v_x_16636__boxed_239_; lean_object* v_res_240_; 
v_x_16635__boxed_238_ = lean_unbox_usize(v_x_234_);
lean_dec(v_x_234_);
v_x_16636__boxed_239_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_233_, v_x_16635__boxed_238_, v_x_16636__boxed_239_, v_x_236_, v_x_237_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(lean_object* v___f_302_, lean_object* v_mv_303_, lean_object* v_val_304_, lean_object* v_tac_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_fileName_359_; lean_object* v_fileMap_360_; lean_object* v_options_361_; lean_object* v_currRecDepth_362_; lean_object* v_maxRecDepth_363_; lean_object* v_ref_364_; lean_object* v_currNamespace_365_; lean_object* v_openDecls_366_; lean_object* v_initHeartbeats_367_; lean_object* v_maxHeartbeats_368_; lean_object* v_quotContext_369_; lean_object* v_currMacroScope_370_; uint8_t v_diag_371_; lean_object* v_cancelTk_x3f_372_; uint8_t v_suppressElabErrors_373_; lean_object* v_inheritedTraceOptions_374_; lean_object* v_keyedConfig_375_; uint8_t v_trackZetaDelta_376_; lean_object* v_zetaDeltaSet_377_; lean_object* v_lctx_378_; lean_object* v_localInstances_379_; lean_object* v_defEqCtx_x3f_380_; lean_object* v_synthPendingDepth_381_; lean_object* v_customCanUnfoldPredicate_x3f_382_; uint8_t v_univApprox_383_; uint8_t v_inTypeClassResolution_384_; uint8_t v_cacheInferType_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v_ref_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_313_ = lean_box(0);
v___x_314_ = lean_box(0);
v___x_315_ = 1;
v___x_319_ = lean_box(1);
v___x_320_ = 0;
v___x_357_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2));
v___x_358_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_358_, 0, v___x_313_);
lean_ctor_set(v___x_358_, 1, v___x_314_);
lean_ctor_set(v___x_358_, 2, v___x_313_);
lean_ctor_set(v___x_358_, 3, v___f_302_);
lean_ctor_set(v___x_358_, 4, v___x_319_);
lean_ctor_set(v___x_358_, 5, v___x_319_);
lean_ctor_set(v___x_358_, 6, v___x_313_);
lean_ctor_set(v___x_358_, 7, v___x_357_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8, v___x_315_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 1, v___x_315_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 2, v___x_315_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 3, v___x_315_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 4, v___x_320_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 5, v___x_320_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 6, v___x_320_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 7, v___x_320_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 8, v___x_315_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 9, v___x_320_);
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*8 + 10, v___x_315_);
v_fileName_359_ = lean_ctor_get(v___y_310_, 0);
v_fileMap_360_ = lean_ctor_get(v___y_310_, 1);
v_options_361_ = lean_ctor_get(v___y_310_, 2);
v_currRecDepth_362_ = lean_ctor_get(v___y_310_, 3);
v_maxRecDepth_363_ = lean_ctor_get(v___y_310_, 4);
v_ref_364_ = lean_ctor_get(v___y_310_, 5);
v_currNamespace_365_ = lean_ctor_get(v___y_310_, 6);
v_openDecls_366_ = lean_ctor_get(v___y_310_, 7);
v_initHeartbeats_367_ = lean_ctor_get(v___y_310_, 8);
v_maxHeartbeats_368_ = lean_ctor_get(v___y_310_, 9);
v_quotContext_369_ = lean_ctor_get(v___y_310_, 10);
v_currMacroScope_370_ = lean_ctor_get(v___y_310_, 11);
v_diag_371_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*14);
v_cancelTk_x3f_372_ = lean_ctor_get(v___y_310_, 12);
v_suppressElabErrors_373_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_374_ = lean_ctor_get(v___y_310_, 13);
v_keyedConfig_375_ = lean_ctor_get(v___y_308_, 0);
v_trackZetaDelta_376_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7);
v_zetaDeltaSet_377_ = lean_ctor_get(v___y_308_, 1);
v_lctx_378_ = lean_ctor_get(v___y_308_, 2);
v_localInstances_379_ = lean_ctor_get(v___y_308_, 3);
v_defEqCtx_x3f_380_ = lean_ctor_get(v___y_308_, 4);
v_synthPendingDepth_381_ = lean_ctor_get(v___y_308_, 5);
v_customCanUnfoldPredicate_x3f_382_ = lean_ctor_get(v___y_308_, 6);
v_univApprox_383_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_384_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 2);
v_cacheInferType_385_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 3);
v___x_386_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__3));
v___x_387_ = 1;
v_ref_388_ = l_Lean_replaceRef(v_val_304_, v_ref_364_);
lean_inc_ref(v_inheritedTraceOptions_374_);
lean_inc(v_cancelTk_x3f_372_);
lean_inc(v_currMacroScope_370_);
lean_inc(v_quotContext_369_);
lean_inc(v_maxHeartbeats_368_);
lean_inc(v_initHeartbeats_367_);
lean_inc(v_openDecls_366_);
lean_inc(v_currNamespace_365_);
lean_inc(v_maxRecDepth_363_);
lean_inc(v_currRecDepth_362_);
lean_inc_ref(v_options_361_);
lean_inc_ref(v_fileMap_360_);
lean_inc_ref(v_fileName_359_);
v___x_389_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_389_, 0, v_fileName_359_);
lean_ctor_set(v___x_389_, 1, v_fileMap_360_);
lean_ctor_set(v___x_389_, 2, v_options_361_);
lean_ctor_set(v___x_389_, 3, v_currRecDepth_362_);
lean_ctor_set(v___x_389_, 4, v_maxRecDepth_363_);
lean_ctor_set(v___x_389_, 5, v_ref_388_);
lean_ctor_set(v___x_389_, 6, v_currNamespace_365_);
lean_ctor_set(v___x_389_, 7, v_openDecls_366_);
lean_ctor_set(v___x_389_, 8, v_initHeartbeats_367_);
lean_ctor_set(v___x_389_, 9, v_maxHeartbeats_368_);
lean_ctor_set(v___x_389_, 10, v_quotContext_369_);
lean_ctor_set(v___x_389_, 11, v_currMacroScope_370_);
lean_ctor_set(v___x_389_, 12, v_cancelTk_x3f_372_);
lean_ctor_set(v___x_389_, 13, v_inheritedTraceOptions_374_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*14, v_diag_371_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*14 + 1, v_suppressElabErrors_373_);
lean_inc_ref(v_keyedConfig_375_);
v___x_390_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_387_, v_keyedConfig_375_);
lean_inc(v_customCanUnfoldPredicate_x3f_382_);
lean_inc(v_synthPendingDepth_381_);
lean_inc(v_defEqCtx_x3f_380_);
lean_inc_ref(v_localInstances_379_);
lean_inc_ref(v_lctx_378_);
lean_inc(v_zetaDeltaSet_377_);
v___x_391_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_zetaDeltaSet_377_);
lean_ctor_set(v___x_391_, 2, v_lctx_378_);
lean_ctor_set(v___x_391_, 3, v_localInstances_379_);
lean_ctor_set(v___x_391_, 4, v_defEqCtx_x3f_380_);
lean_ctor_set(v___x_391_, 5, v_synthPendingDepth_381_);
lean_ctor_set(v___x_391_, 6, v_customCanUnfoldPredicate_x3f_382_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*7, v_trackZetaDelta_376_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*7 + 1, v_univApprox_383_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*7 + 2, v_inTypeClassResolution_384_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*7 + 3, v_cacheInferType_385_);
lean_inc(v_mv_303_);
v___x_392_ = l_Lean_Elab_runTactic(v_mv_303_, v_tac_305_, v___x_358_, v___x_386_, v___x_391_, v___y_309_, v___x_389_, v___y_311_);
lean_dec_ref_known(v___x_389_, 14);
lean_dec_ref_known(v___x_391_, 7);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref_known(v___x_392_, 1);
goto v___jp_321_;
}
else
{
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref_known(v___x_392_, 1);
goto v___jp_321_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_mv_303_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0));
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_356_; 
v___x_322_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mv_303_, v___y_309_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_356_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_356_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_356_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v___x_327_; 
v___x_327_ = lean_unbox(v_a_323_);
lean_dec(v_a_323_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_330_; 
lean_dec(v_mv_303_);
v___x_328_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_328_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
else
{
lean_object* v___x_332_; lean_object* v_a_333_; 
lean_del_object(v___x_325_);
v___x_332_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mv_303_, v___y_309_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
if (lean_obj_tag(v_a_333_) == 1)
{
lean_object* v_val_334_; lean_object* v___x_335_; 
v_val_334_ = lean_ctor_get(v_a_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v_a_333_, 1);
v___x_335_ = l_Lean_Meta_Sym_unfoldReducible(v_val_334_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = l_Lean_Meta_Sym_shareCommon(v_a_336_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mv_303_, v_a_338_, v___y_309_);
lean_dec_ref(v___x_339_);
goto v___jp_316_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_mv_303_);
v_a_340_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_337_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
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
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_mv_303_);
v_a_348_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_335_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_335_);
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
lean_dec(v_a_333_);
lean_dec(v_mv_303_);
goto v___jp_316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_401_, lean_object* v_mv_402_, lean_object* v_val_403_, lean_object* v_tac_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_401_, v_mv_402_, v_val_403_, v_tac_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v_val_403_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
return v___x_415_;
}
else
{
lean_object* v_key_416_; lean_object* v_value_417_; lean_object* v_tail_418_; uint8_t v___x_419_; 
v_key_416_ = lean_ctor_get(v_x_414_, 0);
v_value_417_ = lean_ctor_get(v_x_414_, 1);
v_tail_418_ = lean_ctor_get(v_x_414_, 2);
v___x_419_ = lean_nat_dec_eq(v_key_416_, v_a_413_);
if (v___x_419_ == 0)
{
v_x_414_ = v_tail_418_;
goto _start;
}
else
{
lean_object* v___x_421_; 
lean_inc(v_value_417_);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v_value_417_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_422_, lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_422_, v_x_423_);
lean_dec(v_x_423_);
lean_dec(v_a_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_buckets_427_; lean_object* v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v_fold_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_buckets_427_ = lean_ctor_get(v_m_425_, 1);
v___x_428_ = lean_array_get_size(v_buckets_427_);
v___x_429_ = lean_uint64_of_nat(v_a_426_);
v___x_430_ = 32ULL;
v___x_431_ = lean_uint64_shift_right(v___x_429_, v___x_430_);
v_fold_432_ = lean_uint64_xor(v___x_429_, v___x_431_);
v___x_433_ = 16ULL;
v___x_434_ = lean_uint64_shift_right(v_fold_432_, v___x_433_);
v___x_435_ = lean_uint64_xor(v_fold_432_, v___x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = lean_usize_of_nat(v___x_428_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_usize_land(v___x_436_, v___x_439_);
v___x_441_ = lean_array_uget_borrowed(v_buckets_427_, v___x_440_);
v___x_442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_426_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_m_443_);
return v_res_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Array_mkArray0(lean_box(0));
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object* v_invariantAlts_510_, lean_object* v_n_511_, lean_object* v_mv_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_527_; lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_510_, v_n_511_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_612_; 
v_val_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_612_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_612_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_612_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___f_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___f_545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0));
v___x_546_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5));
lean_inc(v_val_541_);
v___x_547_ = l_Lean_Syntax_isOfKind(v_val_541_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7));
lean_inc(v_val_541_);
v___x_549_ = l_Lean_Syntax_isOfKind(v_val_541_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec(v_val_541_);
lean_dec(v_mv_512_);
v___x_550_ = lean_box(v___x_549_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
lean_ctor_set(v___x_543_, 0, v___x_550_);
v___x_552_ = v___x_543_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = l_Lean_Syntax_getArg(v_val_541_, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9));
lean_inc(v___x_555_);
v___x_557_ = l_Lean_Syntax_isOfKind(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec(v___x_555_);
lean_dec(v_val_541_);
lean_dec(v_mv_512_);
v___x_558_ = lean_box(v___x_557_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
lean_ctor_set(v___x_543_, 0, v___x_558_);
v___x_560_ = v___x_543_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v_ref_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_args_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_del_object(v___x_543_);
v_ref_562_ = lean_ctor_get(v_a_517_, 5);
v___x_563_ = l_Lean_Syntax_getArg(v___x_555_, v___x_554_);
lean_dec(v___x_555_);
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = l_Lean_Syntax_getArg(v_val_541_, v___x_564_);
v_args_566_ = l_Lean_Syntax_getArgs(v___x_563_);
lean_dec(v___x_563_);
v___x_567_ = l_Lean_SourceInfo_fromRef(v_ref_562_, v___x_547_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11));
v___x_569_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_567_, 11);
v___x_570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_567_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14));
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16));
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18));
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20));
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21));
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_567_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22);
v___x_578_ = l_Array_append___redArg(v___x_577_, v_args_566_);
lean_dec_ref(v_args_566_);
v___x_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_579_, 0, v___x_567_);
lean_ctor_set(v___x_579_, 1, v___x_573_);
lean_ctor_set(v___x_579_, 2, v___x_578_);
v___x_580_ = l_Lean_Syntax_node2(v___x_567_, v___x_574_, v___x_576_, v___x_579_);
v___x_581_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23));
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_567_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_584_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_567_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
v___x_586_ = l_Lean_Syntax_node2(v___x_567_, v___x_584_, v___x_585_, v___x_565_);
v___x_587_ = l_Lean_Syntax_node3(v___x_567_, v___x_573_, v___x_580_, v___x_582_, v___x_586_);
v___x_588_ = l_Lean_Syntax_node1(v___x_567_, v___x_572_, v___x_587_);
v___x_589_ = l_Lean_Syntax_node1(v___x_567_, v___x_571_, v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26));
v___x_591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_567_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_Syntax_node3(v___x_567_, v___x_568_, v___x_570_, v___x_589_, v___x_591_);
v___x_593_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_545_, v_mv_512_, v_val_541_, v___x_592_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_val_541_);
v___y_527_ = v___x_593_;
goto v___jp_526_;
}
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = l_Lean_Syntax_getArg(v_val_541_, v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__28));
v___x_597_ = l_Lean_Syntax_isOfKind(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_dec(v_val_541_);
lean_dec(v_mv_512_);
v___x_598_ = lean_box(v___x_597_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
lean_ctor_set(v___x_543_, 0, v___x_598_);
v___x_600_ = v___x_543_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
else
{
lean_object* v_ref_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
lean_del_object(v___x_543_);
v_ref_602_ = lean_ctor_get(v_a_517_, 5);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = l_Lean_Syntax_getArg(v_val_541_, v___x_603_);
v___x_605_ = 0;
v___x_606_ = l_Lean_SourceInfo_fromRef(v_ref_602_, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_608_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25));
lean_inc(v___x_606_);
v___x_609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
v___x_610_ = l_Lean_Syntax_node2(v___x_606_, v___x_608_, v___x_609_, v___x_604_);
v___x_611_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_545_, v_mv_512_, v_val_541_, v___x_610_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_val_541_);
v___y_527_ = v___x_611_;
goto v___jp_526_;
}
}
}
}
else
{
uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v___x_540_);
lean_dec(v_mv_512_);
v___x_613_ = 0;
v___x_614_ = lean_box(v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
v___jp_520_:
{
if (v___y_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref(v___y_521_);
v___x_523_ = lean_box(v___y_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___y_521_);
return v___x_525_;
}
}
v___jp_526_:
{
if (lean_obj_tag(v___y_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v___y_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___y_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___y_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___y_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_a_532_; lean_object* v___x_534_; 
v_a_532_ = lean_ctor_get(v_a_528_, 0);
lean_inc(v_a_532_);
lean_dec(v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v_a_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; uint8_t v___x_538_; 
v_a_537_ = lean_ctor_get(v___y_527_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___y_527_, 1);
v___x_538_ = l_Lean_Exception_isInterrupt(v_a_537_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
lean_inc(v_a_537_);
v___x_539_ = l_Lean_Exception_isRuntime(v_a_537_);
v___y_521_ = v_a_537_;
v___y_522_ = v___x_539_;
goto v___jp_520_;
}
else
{
v___y_521_ = v_a_537_;
v___y_522_ = v___x_538_;
goto v___jp_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_616_, lean_object* v_n_617_, lean_object* v_mv_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_616_, v_n_617_, v_mv_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_n_617_);
lean_dec_ref(v_invariantAlts_616_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_627_, lean_object* v_m_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_628_, v_a_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_631_, lean_object* v_m_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(v_00_u03b2_631_, v_m_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_m_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_635_, v___y_639_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(v_mvarId_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v_mvarId_644_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_653_, lean_object* v_val_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_653_, v_val_654_, v___y_658_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_663_, lean_object* v_val_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(v_mvarId_663_, v_val_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_673_, lean_object* v_a_674_, lean_object* v_x_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_674_, v_x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_677_, lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_677_, v_a_678_, v_x_679_);
lean_dec(v_x_679_);
lean_dec(v_a_678_);
return v_res_680_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_685_, v_x_686_, v_x_687_);
lean_dec(v_x_687_);
lean_dec_ref(v_x_686_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_691_, v_x_692_, v_x_693_);
return v___x_694_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_695_, lean_object* v_x_696_, size_t v_x_697_, lean_object* v_x_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_696_, v_x_697_, v_x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
size_t v_x_17549__boxed_704_; uint8_t v_res_705_; lean_object* v_r_706_; 
v_x_17549__boxed_704_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_res_705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_700_, v_x_701_, v_x_17549__boxed_704_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_x_701_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, size_t v_x_709_, size_t v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_708_, v_x_709_, v_x_710_, v_x_711_, v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
size_t v_x_17560__boxed_720_; size_t v_x_17561__boxed_721_; lean_object* v_res_722_; 
v_x_17560__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_x_17561__boxed_721_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_res_722_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_714_, v_x_715_, v_x_17560__boxed_720_, v_x_17561__boxed_721_, v_x_718_, v_x_719_);
return v_res_722_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_723_, lean_object* v_keys_724_, lean_object* v_vals_725_, lean_object* v_heq_726_, lean_object* v_i_727_, lean_object* v_k_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_724_, v_i_727_, v_k_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_730_, lean_object* v_keys_731_, lean_object* v_vals_732_, lean_object* v_heq_733_, lean_object* v_i_734_, lean_object* v_k_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_730_, v_keys_731_, v_vals_732_, v_heq_733_, v_i_734_, v_k_735_);
lean_dec(v_k_735_);
lean_dec_ref(v_vals_732_);
lean_dec_ref(v_keys_731_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_738_, lean_object* v_n_739_, lean_object* v_k_740_, lean_object* v_v_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_739_, v_k_740_, v_v_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_743_, size_t v_depth_744_, lean_object* v_keys_745_, lean_object* v_vals_746_, lean_object* v_heq_747_, lean_object* v_i_748_, lean_object* v_entries_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_744_, v_keys_745_, v_vals_746_, v_i_748_, v_entries_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_751_, lean_object* v_depth_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_heq_755_, lean_object* v_i_756_, lean_object* v_entries_757_){
_start:
{
size_t v_depth_boxed_758_; lean_object* v_res_759_; 
v_depth_boxed_758_ = lean_unbox_usize(v_depth_752_);
lean_dec(v_depth_752_);
v_res_759_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_751_, v_depth_boxed_758_, v_keys_753_, v_vals_754_, v_heq_755_, v_i_756_, v_entries_757_);
lean_dec_ref(v_vals_754_);
lean_dec_ref(v_keys_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_761_, v_x_762_, v_x_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
uint8_t v___x_768_; 
v___x_768_ = 0;
return v___x_768_;
}
else
{
lean_object* v_key_769_; lean_object* v_tail_770_; uint8_t v___x_771_; 
v_key_769_ = lean_ctor_get(v_x_767_, 0);
v_tail_770_ = lean_ctor_get(v_x_767_, 2);
v___x_771_ = lean_nat_dec_eq(v_key_769_, v_a_766_);
if (v___x_771_ == 0)
{
v_x_767_ = v_tail_770_;
goto _start;
}
else
{
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_773_, lean_object* v_x_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_773_, v_x_774_);
lean_dec(v_x_774_);
lean_dec(v_a_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
return v_x_777_;
}
else
{
lean_object* v_key_779_; lean_object* v_value_780_; lean_object* v_tail_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_804_; 
v_key_779_ = lean_ctor_get(v_x_778_, 0);
v_value_780_ = lean_ctor_get(v_x_778_, 1);
v_tail_781_ = lean_ctor_get(v_x_778_, 2);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_804_ == 0)
{
v___x_783_ = v_x_778_;
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_tail_781_);
lean_inc(v_value_780_);
lean_inc(v_key_779_);
lean_dec(v_x_778_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v_fold_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_785_ = lean_array_get_size(v_x_777_);
v___x_786_ = lean_uint64_of_nat(v_key_779_);
v___x_787_ = 32ULL;
v___x_788_ = lean_uint64_shift_right(v___x_786_, v___x_787_);
v_fold_789_ = lean_uint64_xor(v___x_786_, v___x_788_);
v___x_790_ = 16ULL;
v___x_791_ = lean_uint64_shift_right(v_fold_789_, v___x_790_);
v___x_792_ = lean_uint64_xor(v_fold_789_, v___x_791_);
v___x_793_ = lean_uint64_to_usize(v___x_792_);
v___x_794_ = lean_usize_of_nat(v___x_785_);
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_sub(v___x_794_, v___x_795_);
v___x_797_ = lean_usize_land(v___x_793_, v___x_796_);
v___x_798_ = lean_array_uget_borrowed(v_x_777_, v___x_797_);
lean_inc(v___x_798_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 2, v___x_798_);
v___x_800_ = v___x_783_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_key_779_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_value_780_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v___x_798_);
v___x_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_array_uset(v_x_777_, v___x_797_, v___x_800_);
v_x_777_ = v___x_801_;
v_x_778_ = v_tail_781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_805_, lean_object* v_source_806_, lean_object* v_target_807_){
_start:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = lean_array_get_size(v_source_806_);
v___x_809_ = lean_nat_dec_lt(v_i_805_, v___x_808_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_source_806_);
lean_dec(v_i_805_);
return v_target_807_;
}
else
{
lean_object* v_es_810_; lean_object* v___x_811_; lean_object* v_source_812_; lean_object* v_target_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_es_810_ = lean_array_fget(v_source_806_, v_i_805_);
v___x_811_ = lean_box(0);
v_source_812_ = lean_array_fset(v_source_806_, v_i_805_, v___x_811_);
v_target_813_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_807_, v_es_810_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_815_ = lean_nat_add(v_i_805_, v___x_814_);
lean_dec(v_i_805_);
v_i_805_ = v___x_815_;
v_source_806_ = v_source_812_;
v_target_807_ = v_target_813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_nbuckets_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_818_ = lean_array_get_size(v_data_817_);
v___x_819_ = lean_unsigned_to_nat(2u);
v_nbuckets_820_ = lean_nat_mul(v___x_818_, v___x_819_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_box(0);
v___x_823_ = lean_mk_array(v_nbuckets_820_, v___x_822_);
v___x_824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_821_, v_data_817_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v_size_828_; lean_object* v_buckets_829_; lean_object* v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; uint64_t v_fold_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v_bkt_843_; uint8_t v___x_844_; 
v_size_828_ = lean_ctor_get(v_m_825_, 0);
v_buckets_829_ = lean_ctor_get(v_m_825_, 1);
v___x_830_ = lean_array_get_size(v_buckets_829_);
v___x_831_ = lean_uint64_of_nat(v_a_826_);
v___x_832_ = 32ULL;
v___x_833_ = lean_uint64_shift_right(v___x_831_, v___x_832_);
v_fold_834_ = lean_uint64_xor(v___x_831_, v___x_833_);
v___x_835_ = 16ULL;
v___x_836_ = lean_uint64_shift_right(v_fold_834_, v___x_835_);
v___x_837_ = lean_uint64_xor(v_fold_834_, v___x_836_);
v___x_838_ = lean_uint64_to_usize(v___x_837_);
v___x_839_ = lean_usize_of_nat(v___x_830_);
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_sub(v___x_839_, v___x_840_);
v___x_842_ = lean_usize_land(v___x_838_, v___x_841_);
v_bkt_843_ = lean_array_uget_borrowed(v_buckets_829_, v___x_842_);
v___x_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_826_, v_bkt_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_865_; 
lean_inc_ref(v_buckets_829_);
lean_inc(v_size_828_);
v_isSharedCheck_865_ = !lean_is_exclusive(v_m_825_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; lean_object* v_unused_867_; 
v_unused_866_ = lean_ctor_get(v_m_825_, 1);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_m_825_, 0);
lean_dec(v_unused_867_);
v___x_846_ = v_m_825_;
v_isShared_847_ = v_isSharedCheck_865_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_m_825_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_865_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_size_x27_849_; lean_object* v___x_850_; lean_object* v_buckets_x27_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_848_ = lean_unsigned_to_nat(1u);
v_size_x27_849_ = lean_nat_add(v_size_828_, v___x_848_);
lean_dec(v_size_828_);
lean_inc(v_bkt_843_);
v___x_850_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_850_, 0, v_a_826_);
lean_ctor_set(v___x_850_, 1, v_b_827_);
lean_ctor_set(v___x_850_, 2, v_bkt_843_);
v_buckets_x27_851_ = lean_array_uset(v_buckets_829_, v___x_842_, v___x_850_);
v___x_852_ = lean_unsigned_to_nat(4u);
v___x_853_ = lean_nat_mul(v_size_x27_849_, v___x_852_);
v___x_854_ = lean_unsigned_to_nat(3u);
v___x_855_ = lean_nat_div(v___x_853_, v___x_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_array_get_size(v_buckets_x27_851_);
v___x_857_ = lean_nat_dec_le(v___x_855_, v___x_856_);
lean_dec(v___x_855_);
if (v___x_857_ == 0)
{
lean_object* v_val_858_; lean_object* v___x_860_; 
v_val_858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_851_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_val_858_);
lean_ctor_set(v___x_846_, 0, v_size_x27_849_);
v___x_860_ = v___x_846_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_size_x27_849_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_val_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v___x_863_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_buckets_x27_851_);
lean_ctor_set(v___x_846_, 0, v_size_x27_849_);
v___x_863_ = v___x_846_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_size_x27_849_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_buckets_x27_851_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_dec(v_b_827_);
lean_dec(v_a_826_);
return v_m_825_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_868_, lean_object* v_as_x27_869_, lean_object* v_b_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
if (lean_obj_tag(v_as_x27_869_) == 0)
{
lean_object* v___x_880_; 
lean_dec_ref(v___x_868_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_b_870_);
return v___x_880_;
}
else
{
lean_object* v_head_881_; lean_object* v_tail_882_; lean_object* v___x_883_; 
v_head_881_ = lean_ctor_get(v_as_x27_869_, 0);
v_tail_882_ = lean_ctor_get(v_as_x27_869_, 1);
lean_inc(v_head_881_);
v___x_883_ = l_Lean_MVarId_getType(v_head_881_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; uint8_t v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc_ref(v___x_868_);
v___x_885_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_868_, v_a_884_);
lean_dec(v_a_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_inc(v_head_881_);
v___x_886_ = lean_array_push(v_b_870_, v_head_881_);
v_as_x27_869_ = v_tail_882_;
v_b_870_ = v___x_886_;
goto _start;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_specBackwardRuleCache_890_; lean_object* v_splitBackwardRuleCache_891_; lean_object* v_latticeBackwardRuleCache_892_; lean_object* v_frameBackwardRuleCache_893_; lean_object* v_frameDB_894_; lean_object* v_invariants_895_; lean_object* v_vcs_896_; lean_object* v_simpState_897_; lean_object* v_fuel_898_; lean_object* v_inlineHandledInvariants_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_957_; 
v___x_888_ = lean_st_ref_get(v___y_872_);
v___x_889_ = lean_st_ref_take(v___y_872_);
v_specBackwardRuleCache_890_ = lean_ctor_get(v___x_889_, 0);
v_splitBackwardRuleCache_891_ = lean_ctor_get(v___x_889_, 1);
v_latticeBackwardRuleCache_892_ = lean_ctor_get(v___x_889_, 2);
v_frameBackwardRuleCache_893_ = lean_ctor_get(v___x_889_, 3);
v_frameDB_894_ = lean_ctor_get(v___x_889_, 4);
v_invariants_895_ = lean_ctor_get(v___x_889_, 5);
v_vcs_896_ = lean_ctor_get(v___x_889_, 6);
v_simpState_897_ = lean_ctor_get(v___x_889_, 7);
v_fuel_898_ = lean_ctor_get(v___x_889_, 8);
v_inlineHandledInvariants_899_ = lean_ctor_get(v___x_889_, 9);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_957_ == 0)
{
v___x_901_ = v___x_889_;
v_isShared_902_ = v_isSharedCheck_957_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_inlineHandledInvariants_899_);
lean_inc(v_fuel_898_);
lean_inc(v_simpState_897_);
lean_inc(v_vcs_896_);
lean_inc(v_invariants_895_);
lean_inc(v_frameDB_894_);
lean_inc(v_frameBackwardRuleCache_893_);
lean_inc(v_latticeBackwardRuleCache_892_);
lean_inc(v_splitBackwardRuleCache_891_);
lean_inc(v_specBackwardRuleCache_890_);
lean_dec(v___x_889_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_957_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
lean_inc(v_head_881_);
v___x_903_ = lean_array_push(v_invariants_895_, v_head_881_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 5, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_specBackwardRuleCache_890_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_splitBackwardRuleCache_891_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_latticeBackwardRuleCache_892_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_frameBackwardRuleCache_893_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_frameDB_894_);
lean_ctor_set(v_reuseFailAlloc_956_, 5, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_956_, 6, v_vcs_896_);
lean_ctor_set(v_reuseFailAlloc_956_, 7, v_simpState_897_);
lean_ctor_set(v_reuseFailAlloc_956_, 8, v_fuel_898_);
lean_ctor_set(v_reuseFailAlloc_956_, 9, v_inlineHandledInvariants_899_);
v___x_905_ = v_reuseFailAlloc_956_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v_invariants_907_; lean_object* v_invariantAlts_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_906_ = lean_st_ref_set(v___y_872_, v___x_905_);
v_invariants_907_ = lean_ctor_get(v___x_888_, 5);
lean_inc_ref(v_invariants_907_);
lean_dec(v___x_888_);
v_invariantAlts_908_ = lean_ctor_get(v___y_871_, 4);
v___x_909_ = lean_array_get_size(v_invariants_907_);
lean_dec_ref(v_invariants_907_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_add(v___x_909_, v___x_910_);
lean_inc(v_head_881_);
v___x_912_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_908_, v___x_911_, v_head_881_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; lean_object* v___x_916_; 
lean_dec(v___x_911_);
v___x_915_ = 2;
lean_inc(v_head_881_);
v___x_916_ = l_Lean_MVarId_setKind___redArg(v_head_881_, v___x_915_, v___y_876_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_dec_ref_known(v___x_916_, 1);
v_as_x27_869_ = v_tail_882_;
goto _start;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v_b_870_);
lean_dec_ref(v___x_868_);
v_a_918_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_916_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_926_; lean_object* v_specBackwardRuleCache_927_; lean_object* v_splitBackwardRuleCache_928_; lean_object* v_latticeBackwardRuleCache_929_; lean_object* v_frameBackwardRuleCache_930_; lean_object* v_frameDB_931_; lean_object* v_invariants_932_; lean_object* v_vcs_933_; lean_object* v_simpState_934_; lean_object* v_fuel_935_; lean_object* v_inlineHandledInvariants_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_947_; 
v___x_926_ = lean_st_ref_take(v___y_872_);
v_specBackwardRuleCache_927_ = lean_ctor_get(v___x_926_, 0);
v_splitBackwardRuleCache_928_ = lean_ctor_get(v___x_926_, 1);
v_latticeBackwardRuleCache_929_ = lean_ctor_get(v___x_926_, 2);
v_frameBackwardRuleCache_930_ = lean_ctor_get(v___x_926_, 3);
v_frameDB_931_ = lean_ctor_get(v___x_926_, 4);
v_invariants_932_ = lean_ctor_get(v___x_926_, 5);
v_vcs_933_ = lean_ctor_get(v___x_926_, 6);
v_simpState_934_ = lean_ctor_get(v___x_926_, 7);
v_fuel_935_ = lean_ctor_get(v___x_926_, 8);
v_inlineHandledInvariants_936_ = lean_ctor_get(v___x_926_, 9);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_947_ == 0)
{
v___x_938_ = v___x_926_;
v_isShared_939_ = v_isSharedCheck_947_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_inlineHandledInvariants_936_);
lean_inc(v_fuel_935_);
lean_inc(v_simpState_934_);
lean_inc(v_vcs_933_);
lean_inc(v_invariants_932_);
lean_inc(v_frameDB_931_);
lean_inc(v_frameBackwardRuleCache_930_);
lean_inc(v_latticeBackwardRuleCache_929_);
lean_inc(v_splitBackwardRuleCache_928_);
lean_inc(v_specBackwardRuleCache_927_);
lean_dec(v___x_926_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_947_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_box(0);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_936_, v___x_911_, v___x_940_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 9, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_specBackwardRuleCache_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_splitBackwardRuleCache_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_latticeBackwardRuleCache_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_frameBackwardRuleCache_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_frameDB_931_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_invariants_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_vcs_933_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_simpState_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v_fuel_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 9, v___x_941_);
v___x_943_ = v_reuseFailAlloc_946_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_st_ref_set(v___y_872_, v___x_943_);
v_as_x27_869_ = v_tail_882_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v___x_911_);
lean_dec_ref(v_b_870_);
lean_dec_ref(v___x_868_);
v_a_948_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_912_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_912_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec_ref(v_b_870_);
lean_dec_ref(v___x_868_);
v_a_958_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_883_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_883_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_966_, lean_object* v_as_x27_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_966_, v_as_x27_967_, v_b_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v_as_x27_967_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; lean_object* v_env_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = lean_st_ref_get(v_a_992_);
v_env_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc_ref(v_env_995_);
lean_dec(v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_997_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_995_, v_subgoals_981_, v___x_996_, v_a_982_, v_a_983_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_subgoals_998_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1012_, lean_object* v_m_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1013_, v_a_1014_, v_b_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1017_, lean_object* v_as_1018_, lean_object* v_as_x27_1019_, lean_object* v_b_1020_, lean_object* v_a_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1017_, v_as_x27_1019_, v_b_1020_, v___y_1022_, v___y_1023_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1035_ = _args[0];
lean_object* v_as_1036_ = _args[1];
lean_object* v_as_x27_1037_ = _args[2];
lean_object* v_b_1038_ = _args[3];
lean_object* v_a_1039_ = _args[4];
lean_object* v___y_1040_ = _args[5];
lean_object* v___y_1041_ = _args[6];
lean_object* v___y_1042_ = _args[7];
lean_object* v___y_1043_ = _args[8];
lean_object* v___y_1044_ = _args[9];
lean_object* v___y_1045_ = _args[10];
lean_object* v___y_1046_ = _args[11];
lean_object* v___y_1047_ = _args[12];
lean_object* v___y_1048_ = _args[13];
lean_object* v___y_1049_ = _args[14];
lean_object* v___y_1050_ = _args[15];
lean_object* v___y_1051_ = _args[16];
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(v___x_1035_, v_as_1036_, v_as_x27_1037_, v_b_1038_, v_a_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v_as_x27_1037_);
lean_dec(v_as_1036_);
return v_res_1052_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1053_, lean_object* v_a_1054_, lean_object* v_x_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1057_, lean_object* v_a_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1057_, v_a_1058_, v_x_1059_);
lean_dec(v_x_1059_);
lean_dec(v_a_1058_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1062_, lean_object* v_data_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1065_, lean_object* v_i_1066_, lean_object* v_source_1067_, lean_object* v_target_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1066_, v_source_1067_, v_target_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1071_, v_x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object* v_goal_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_toGoalState_1087_; lean_object* v_mvarId_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1188_; 
v_toGoalState_1087_ = lean_ctor_get(v_goal_1074_, 0);
v_mvarId_1088_ = lean_ctor_get(v_goal_1074_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_goal_1074_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1090_ = v_goal_1074_;
v_isShared_1091_ = v_isSharedCheck_1188_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_mvarId_1088_);
lean_inc(v_toGoalState_1087_);
lean_dec(v_goal_1074_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1188_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elimTopPre___redArg(v_mvarId_1088_, v_a_1075_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_a_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_toGoalState_1087_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_a_1093_);
v___x_1095_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v___x_1095_, v_a_1075_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1170_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1170_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1170_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_toGoalState_1101_; lean_object* v_mvarId_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1169_; 
v_toGoalState_1101_ = lean_ctor_get(v_a_1097_, 0);
v_mvarId_1102_ = lean_ctor_get(v_a_1097_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_a_1097_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1104_ = v_a_1097_;
v_isShared_1105_ = v_isSharedCheck_1169_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_mvarId_1102_);
lean_inc(v_toGoalState_1101_);
lean_dec(v_a_1097_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1169_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_mvarId_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; uint8_t v_inconsistent_1144_; 
v_inconsistent_1144_ = lean_ctor_get_uint8(v_toGoalState_1101_, sizeof(void*)*17);
if (v_inconsistent_1144_ == 0)
{
uint8_t v_trivial_1145_; 
lean_del_object(v___x_1099_);
v_trivial_1145_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*6);
if (v_trivial_1145_ == 0)
{
v_mvarId_1107_ = v_mvarId_1102_;
v___y_1108_ = v_a_1076_;
v___y_1109_ = v_a_1083_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_mvarId_1102_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1156_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1156_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1156_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
if (lean_obj_tag(v_a_1147_) == 1)
{
lean_object* v_val_1151_; 
lean_del_object(v___x_1149_);
v_val_1151_ = lean_ctor_get(v_a_1147_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v_a_1147_, 1);
v_mvarId_1107_ = v_val_1151_;
v___y_1108_ = v_a_1076_;
v___y_1109_ = v_a_1083_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec(v_a_1147_);
lean_del_object(v___x_1104_);
lean_dec_ref(v_toGoalState_1101_);
v___x_1152_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_del_object(v___x_1104_);
lean_dec_ref(v_toGoalState_1101_);
v_a_1157_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1146_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1146_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_del_object(v___x_1104_);
lean_dec(v_mvarId_1102_);
lean_dec_ref(v_toGoalState_1101_);
v___x_1165_ = lean_box(0);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1165_);
v___x_1167_ = v___x_1099_;
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
v___jp_1106_:
{
uint8_t v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = 2;
lean_inc(v_mvarId_1107_);
v___x_1111_ = l_Lean_MVarId_setKind___redArg(v_mvarId_1107_, v___x_1110_, v___y_1109_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1142_; 
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1111_, 0);
lean_dec(v_unused_1143_);
v___x_1113_ = v___x_1111_;
v_isShared_1114_ = v_isSharedCheck_1142_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v___x_1111_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1142_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v_specBackwardRuleCache_1116_; lean_object* v_splitBackwardRuleCache_1117_; lean_object* v_latticeBackwardRuleCache_1118_; lean_object* v_frameBackwardRuleCache_1119_; lean_object* v_frameDB_1120_; lean_object* v_invariants_1121_; lean_object* v_vcs_1122_; lean_object* v_simpState_1123_; lean_object* v_fuel_1124_; lean_object* v_inlineHandledInvariants_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1141_; 
v___x_1115_ = lean_st_ref_take(v___y_1108_);
v_specBackwardRuleCache_1116_ = lean_ctor_get(v___x_1115_, 0);
v_splitBackwardRuleCache_1117_ = lean_ctor_get(v___x_1115_, 1);
v_latticeBackwardRuleCache_1118_ = lean_ctor_get(v___x_1115_, 2);
v_frameBackwardRuleCache_1119_ = lean_ctor_get(v___x_1115_, 3);
v_frameDB_1120_ = lean_ctor_get(v___x_1115_, 4);
v_invariants_1121_ = lean_ctor_get(v___x_1115_, 5);
v_vcs_1122_ = lean_ctor_get(v___x_1115_, 6);
v_simpState_1123_ = lean_ctor_get(v___x_1115_, 7);
v_fuel_1124_ = lean_ctor_get(v___x_1115_, 8);
v_inlineHandledInvariants_1125_ = lean_ctor_get(v___x_1115_, 9);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1127_ = v___x_1115_;
v_isShared_1128_ = v_isSharedCheck_1141_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_inlineHandledInvariants_1125_);
lean_inc(v_fuel_1124_);
lean_inc(v_simpState_1123_);
lean_inc(v_vcs_1122_);
lean_inc(v_invariants_1121_);
lean_inc(v_frameDB_1120_);
lean_inc(v_frameBackwardRuleCache_1119_);
lean_inc(v_latticeBackwardRuleCache_1118_);
lean_inc(v_splitBackwardRuleCache_1117_);
lean_inc(v_specBackwardRuleCache_1116_);
lean_dec(v___x_1115_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1141_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v_mvarId_1107_);
v___x_1130_ = v___x_1104_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_toGoalState_1101_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_mvarId_1107_);
v___x_1130_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_array_push(v_vcs_1122_, v___x_1130_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 6, v___x_1131_);
v___x_1133_ = v___x_1127_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_specBackwardRuleCache_1116_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_splitBackwardRuleCache_1117_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_latticeBackwardRuleCache_1118_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_frameBackwardRuleCache_1119_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_frameDB_1120_);
lean_ctor_set(v_reuseFailAlloc_1139_, 5, v_invariants_1121_);
lean_ctor_set(v_reuseFailAlloc_1139_, 6, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 7, v_simpState_1123_);
lean_ctor_set(v_reuseFailAlloc_1139_, 8, v_fuel_1124_);
lean_ctor_set(v_reuseFailAlloc_1139_, 9, v_inlineHandledInvariants_1125_);
v___x_1133_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1134_ = lean_st_ref_set(v___y_1108_, v___x_1133_);
v___x_1135_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1135_);
v___x_1137_ = v___x_1113_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
else
{
lean_dec(v_mvarId_1107_);
lean_del_object(v___x_1104_);
lean_dec_ref(v_toGoalState_1101_);
return v___x_1111_;
}
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1096_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1096_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_del_object(v___x_1090_);
lean_dec_ref(v_toGoalState_1087_);
v_a_1180_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1092_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1092_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object* v_goal_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object* v_goal_1203_, lean_object* v_scope_1204_, size_t v_sz_1205_, size_t v_i_1206_, lean_object* v_bs_1207_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_usize_dec_lt(v_i_1206_, v_sz_1205_);
if (v___x_1208_ == 0)
{
lean_dec_ref(v_scope_1204_);
return v_bs_1207_;
}
else
{
lean_object* v_toGoalState_1209_; lean_object* v_v_1210_; lean_object* v___x_1211_; lean_object* v_bs_x27_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v_toGoalState_1209_ = lean_ctor_get(v_goal_1203_, 0);
v_v_1210_ = lean_array_uget(v_bs_1207_, v_i_1206_);
v___x_1211_ = lean_unsigned_to_nat(0u);
v_bs_x27_1212_ = lean_array_uset(v_bs_1207_, v_i_1206_, v___x_1211_);
lean_inc_ref(v_toGoalState_1209_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_toGoalState_1209_);
lean_ctor_set(v___x_1213_, 1, v_v_1210_);
lean_inc_ref(v_scope_1204_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v_scope_1204_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1206_, v___x_1215_);
v___x_1217_ = lean_array_uset(v_bs_x27_1212_, v_i_1206_, v___x_1214_);
v_i_1206_ = v___x_1216_;
v_bs_1207_ = v___x_1217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object* v_goal_1219_, lean_object* v_scope_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_bs_1223_){
_start:
{
size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_goal_1219_, v_scope_1220_, v_sz_boxed_1224_, v_i_boxed_1225_, v_bs_1223_);
lean_dec_ref(v_goal_1219_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(lean_object* v_a_1227_, lean_object* v_scope_1228_, lean_object* v___x_1229_, lean_object* v_goal_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; size_t v_sz_1244_; size_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1243_ = l_Array_reverse___redArg(v_a_1227_);
v_sz_1244_ = lean_array_size(v___x_1243_);
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_goal_1230_, v_scope_1228_, v_sz_1244_, v___x_1245_, v___x_1243_);
v___x_1247_ = l_Array_append___redArg(v___x_1229_, v___x_1246_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0___boxed(lean_object* v_a_1250_, lean_object* v_scope_1251_, lean_object* v___x_1252_, lean_object* v_goal_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1250_, v_scope_1251_, v___x_1252_, v_goal_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec_ref(v_goal_1253_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(lean_object* v_a_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___y_1281_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1301_ = lean_array_get_size(v_a_1267_);
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_sub(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_nat_dec_lt(v___x_1303_, v___x_1301_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v___x_1303_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_a_1267_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; lean_object* v_goal_1307_; lean_object* v_toGoalState_1308_; lean_object* v_scope_1309_; lean_object* v_mvarId_1310_; uint8_t v_inconsistent_1311_; lean_object* v___x_1312_; 
v___x_1306_ = lean_array_fget_borrowed(v_a_1267_, v___x_1303_);
lean_dec(v___x_1303_);
v_goal_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_goal_1307_);
v_toGoalState_1308_ = lean_ctor_get(v_goal_1307_, 0);
v_scope_1309_ = lean_ctor_get(v___x_1306_, 1);
lean_inc_ref(v_scope_1309_);
v_mvarId_1310_ = lean_ctor_get(v_goal_1307_, 1);
v_inconsistent_1311_ = lean_ctor_get_uint8(v_toGoalState_1308_, sizeof(void*)*17);
v___x_1312_ = lean_array_pop(v_a_1267_);
if (v_inconsistent_1311_ == 0)
{
lean_object* v___x_1313_; 
lean_inc(v_mvarId_1310_);
v___x_1313_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_1309_, v_mvarId_1310_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
if (lean_obj_tag(v_a_1314_) == 0)
{
lean_object* v_scope_1315_; lean_object* v_subgoals_1316_; lean_object* v___x_1317_; 
v_scope_1315_ = lean_ctor_get(v_a_1314_, 0);
lean_inc_ref(v_scope_1315_);
v_subgoals_1316_ = lean_ctor_get(v_a_1314_, 1);
lean_inc(v_subgoals_1316_);
lean_dec_ref_known(v_a_1314_, 2);
v___x_1317_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1316_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v_subgoals_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_array_get_size(v_a_1318_);
v___x_1320_ = lean_nat_dec_lt(v___x_1302_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1318_, v_scope_1315_, v___x_1312_, v_goal_1307_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec_ref(v_goal_1307_);
v___y_1281_ = v___x_1321_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_1307_, v___y_1268_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___lam__0(v_a_1318_, v_scope_1315_, v___x_1312_, v_a_1323_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v_a_1323_);
v___y_1281_ = v___x_1324_;
goto v___jp_1280_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1318_);
lean_dec_ref(v_scope_1315_);
lean_dec_ref(v___x_1312_);
v_a_1325_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1322_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_scope_1315_);
lean_dec_ref(v___x_1312_);
lean_dec_ref(v_goal_1307_);
v_a_1333_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1317_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1317_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref_known(v_a_1314_, 1);
v___x_1341_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1307_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref_known(v___x_1341_, 1);
v_a_1267_ = v___x_1312_;
goto _start;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v___x_1312_);
v_a_1343_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1341_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v___x_1312_);
lean_dec_ref(v_goal_1307_);
v_a_1351_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1313_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1313_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1309_);
lean_dec_ref(v_goal_1307_);
v_a_1267_ = v___x_1312_;
goto _start;
}
}
v___jp_1280_:
{
if (lean_obj_tag(v___y_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1292_; 
v_a_1282_ = lean_ctor_get(v___y_1281_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___y_1281_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1284_ = v___y_1281_;
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___y_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
if (lean_obj_tag(v_a_1282_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; 
v_a_1286_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v_a_1282_, 1);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_a_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
else
{
lean_object* v_a_1290_; 
lean_del_object(v___x_1284_);
v_a_1290_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v_a_1282_, 1);
v_a_1267_ = v_a_1290_;
goto _start;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___y_1281_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___y_1281_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___y_1281_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___y_1281_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg___boxed(lean_object* v_a_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v_a_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object* v_scope_1374_, lean_object* v_goal_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_toGoalState_1388_; lean_object* v_mvarId_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1428_; 
v_toGoalState_1388_ = lean_ctor_get(v_goal_1375_, 0);
v_mvarId_1389_ = lean_ctor_get(v_goal_1375_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_goal_1375_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1391_ = v_goal_1375_;
v_isShared_1392_ = v_isSharedCheck_1428_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_mvarId_1389_);
lean_inc(v_toGoalState_1388_);
lean_dec(v_goal_1375_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1428_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1389_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 1, v_a_1394_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_toGoalState_1388_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_a_1394_);
v___x_1396_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_scope_1374_);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1400_ = lean_array_push(v___x_1399_, v___x_1397_);
v___x_1401_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v___x_1400_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1410_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_box(0);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1401_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1401_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1391_);
lean_dec_ref(v_toGoalState_1388_);
lean_dec_ref(v_scope_1374_);
v_a_1420_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1393_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1393_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object* v_scope_1429_, lean_object* v_goal_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_1429_, v_goal_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(lean_object* v_inst_1444_, lean_object* v_a_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___redArg(v_a_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object* v_inst_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_inst_1459_, v_a_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(lean_object* v_x_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_config_1485_; lean_object* v_sharedExprs_1486_; uint8_t v_verbose_1487_; uint8_t v_enforceUnfoldReducible_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_config_1485_ = lean_ctor_get(v___y_1478_, 1);
v_sharedExprs_1486_ = lean_ctor_get(v___y_1478_, 0);
v_verbose_1487_ = lean_ctor_get_uint8(v_config_1485_, 0);
v_enforceUnfoldReducible_1488_ = lean_ctor_get_uint8(v_config_1485_, 1);
v___x_1489_ = 0;
v___x_1490_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_1490_, 0, v_verbose_1487_);
lean_ctor_set_uint8(v___x_1490_, 1, v_enforceUnfoldReducible_1488_);
lean_ctor_set_uint8(v___x_1490_, 2, v___x_1489_);
lean_inc_ref(v_sharedExprs_1486_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_sharedExprs_1486_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
v___x_1492_ = lean_apply_10(v_x_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___x_1491_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_x_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object* v_00_u03b1_1505_, lean_object* v_x_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_x_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(v_00_u03b1_1518_, v_x_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(lean_object* v_initState_1531_, lean_object* v_scope_1532_, lean_object* v_goal_1533_, lean_object* v_ctx_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_st_mk_ref(v_initState_1531_);
v___x_1546_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_1532_, v_goal_1533_, v_ctx_1534_, v___x_1545_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1556_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1556_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1556_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1551_ = lean_st_ref_get(v___x_1545_);
lean_dec(v___x_1545_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1547_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v___x_1545_);
v_a_1557_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1546_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1546_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___boxed(lean_object* v_initState_1565_, lean_object* v_scope_1566_, lean_object* v_goal_1567_, lean_object* v_ctx_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0(v_initState_1565_, v_scope_1566_, v_goal_1567_, v_ctx_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v_ctx_1568_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v_mctx_1584_; lean_object* v_eAssignment_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1583_ = lean_st_ref_get(v___y_1581_);
v_mctx_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_ref(v_mctx_1584_);
lean_dec(v___x_1583_);
v_eAssignment_1585_ = lean_ctor_get(v_mctx_1584_, 8);
lean_inc_ref(v_eAssignment_1585_);
lean_dec_ref(v_mctx_1584_);
v___x_1586_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1585_, v_mvarId_1580_);
lean_dec_ref(v_eAssignment_1585_);
v___x_1587_ = lean_box(v___x_1586_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec(v_mvarId_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5(lean_object* v_as_1593_, size_t v_i_1594_, size_t v_stop_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_a_1608_; uint8_t v___x_1612_; 
v___x_1612_ = lean_usize_dec_eq(v_i_1594_, v_stop_1595_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v_mvarId_1616_; lean_object* v___x_1617_; 
v___x_1613_ = lean_array_uget_borrowed(v_as_1593_, v_i_1594_);
v_mvarId_1616_ = lean_ctor_get(v___x_1613_, 1);
v___x_1617_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1616_, v___y_1603_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = lean_unbox(v_a_1618_);
lean_dec(v_a_1618_);
if (v___x_1619_ == 0)
{
goto v___jp_1614_;
}
else
{
v_a_1608_ = v_b_1596_;
goto v___jp_1607_;
}
}
else
{
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1621_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
if (v___x_1621_ == 0)
{
v_a_1608_ = v_b_1596_;
goto v___jp_1607_;
}
else
{
goto v___jp_1614_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_b_1596_);
v_a_1622_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1617_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1617_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
v___jp_1614_:
{
lean_object* v___x_1615_; 
lean_inc(v___x_1613_);
v___x_1615_ = lean_array_push(v_b_1596_, v___x_1613_);
v_a_1608_ = v___x_1615_;
goto v___jp_1607_;
}
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_b_1596_);
return v___x_1630_;
}
v___jp_1607_:
{
size_t v___x_1609_; size_t v___x_1610_; 
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_add(v_i_1594_, v___x_1609_);
v_i_1594_ = v___x_1610_;
v_b_1596_ = v_a_1608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5___boxed(lean_object* v_as_1631_, lean_object* v_i_1632_, lean_object* v_stop_1633_, lean_object* v_b_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
size_t v_i_boxed_1645_; size_t v_stop_boxed_1646_; lean_object* v_res_1647_; 
v_i_boxed_1645_ = lean_unbox_usize(v_i_1632_);
lean_dec(v_i_1632_);
v_stop_boxed_1646_ = lean_unbox_usize(v_stop_1633_);
lean_dec(v_stop_1633_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5(v_as_1631_, v_i_boxed_1645_, v_stop_boxed_1646_, v_b_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v_as_1631_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg(size_t v_sz_1649_, size_t v_i_1650_, lean_object* v_bs_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
uint8_t v___x_1657_; 
v___x_1657_ = lean_usize_dec_lt(v_i_1650_, v_sz_1649_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_bs_1651_);
return v___x_1658_;
}
else
{
lean_object* v_v_1659_; lean_object* v_mvarId_1660_; lean_object* v___x_1661_; 
v_v_1659_ = lean_array_uget_borrowed(v_bs_1651_, v_i_1650_);
v_mvarId_1660_ = lean_ctor_get(v_v_1659_, 1);
lean_inc_n(v_mvarId_1660_, 2);
v___x_1661_ = l_Lean_MVarId_getTag(v_mvarId_1660_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; lean_object* v_bs_x27_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = lean_unsigned_to_nat(0u);
v_bs_x27_1664_ = lean_array_uset(v_bs_1651_, v_i_1650_, v___x_1663_);
v___x_1665_ = lean_usize_to_nat(v_i_1650_);
v___x_1666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg___closed__0));
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v___x_1665_, v___x_1667_);
lean_dec(v___x_1665_);
v___x_1669_ = l_Nat_reprFast(v___x_1668_);
v___x_1670_ = lean_string_append(v___x_1666_, v___x_1669_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Lean_Name_str___override(v___x_1671_, v___x_1670_);
v___x_1673_ = l_Lean_Name_eraseMacroScopes(v_a_1662_);
lean_dec(v_a_1662_);
v___x_1674_ = l_Lean_Name_append(v___x_1672_, v___x_1673_);
v___x_1675_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1660_, v___x_1674_, v___y_1653_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1650_, v___x_1677_);
v___x_1679_ = lean_array_uset(v_bs_x27_1664_, v_i_1650_, v_a_1676_);
v_i_1650_ = v___x_1678_;
v_bs_1651_ = v___x_1679_;
goto _start;
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_bs_x27_1664_);
v_a_1681_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1675_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1675_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_mvarId_1660_);
lean_dec_ref(v_bs_1651_);
v_a_1689_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1661_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1661_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_1697_, lean_object* v_i_1698_, lean_object* v_bs_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
size_t v_sz_boxed_1705_; size_t v_i_boxed_1706_; lean_object* v_res_1707_; 
v_sz_boxed_1705_ = lean_unbox_usize(v_sz_1697_);
lean_dec(v_sz_1697_);
v_i_boxed_1706_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg(v_sz_boxed_1705_, v_i_boxed_1706_, v_bs_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(size_t v_sz_1709_, size_t v_i_1710_, lean_object* v_bs_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_lt(v_i_1710_, v_sz_1709_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_bs_1711_);
return v___x_1715_;
}
else
{
lean_object* v_v_1716_; lean_object* v___x_1717_; lean_object* v_bs_x27_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_v_1716_ = lean_array_uget(v_bs_1711_, v_i_1710_);
v___x_1717_ = lean_unsigned_to_nat(0u);
v_bs_x27_1718_ = lean_array_uset(v_bs_1711_, v_i_1710_, v___x_1717_);
v___x_1719_ = lean_usize_to_nat(v_i_1710_);
v___x_1720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___closed__0));
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_nat_add(v___x_1719_, v___x_1721_);
lean_dec(v___x_1719_);
v___x_1723_ = l_Nat_reprFast(v___x_1722_);
v___x_1724_ = lean_string_append(v___x_1720_, v___x_1723_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = lean_box(0);
v___x_1726_ = l_Lean_Name_str___override(v___x_1725_, v___x_1724_);
v___x_1727_ = l_Lean_MVarId_setTag___redArg(v_v_1716_, v___x_1726_, v___y_1712_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = ((size_t)1ULL);
v___x_1730_ = lean_usize_add(v_i_1710_, v___x_1729_);
v___x_1731_ = lean_array_uset(v_bs_x27_1718_, v_i_1710_, v_a_1728_);
v_i_1710_ = v___x_1730_;
v_bs_1711_ = v___x_1731_;
goto _start;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v_bs_x27_1718_);
v_a_1733_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1727_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1727_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1741_, lean_object* v_i_1742_, lean_object* v_bs_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1741_);
lean_dec(v_sz_1741_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(v_sz_boxed_1746_, v_i_boxed_1747_, v_bs_1743_, v___y_1744_);
lean_dec(v___y_1744_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2(lean_object* v_as_1749_, size_t v_i_1750_, size_t v_stop_1751_, lean_object* v_b_1752_){
_start:
{
lean_object* v___y_1754_; uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_eq(v_i_1750_, v_stop_1751_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v_retired_1760_; 
v___x_1759_ = lean_array_uget_borrowed(v_as_1749_, v_i_1750_);
v_retired_1760_ = lean_ctor_get_uint8(v___x_1759_, sizeof(void*)*4);
if (v_retired_1760_ == 0)
{
lean_object* v_frameStx_1761_; lean_object* v___x_1762_; 
v_frameStx_1761_ = lean_ctor_get(v___x_1759_, 2);
lean_inc(v_frameStx_1761_);
v___x_1762_ = lean_array_push(v_b_1752_, v_frameStx_1761_);
v___y_1754_ = v___x_1762_;
goto v___jp_1753_;
}
else
{
v___y_1754_ = v_b_1752_;
goto v___jp_1753_;
}
}
else
{
return v_b_1752_;
}
v___jp_1753_:
{
size_t v___x_1755_; size_t v___x_1756_; 
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1750_, v___x_1755_);
v_i_1750_ = v___x_1756_;
v_b_1752_ = v___y_1754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_1763_, lean_object* v_i_1764_, lean_object* v_stop_1765_, lean_object* v_b_1766_){
_start:
{
size_t v_i_boxed_1767_; size_t v_stop_boxed_1768_; lean_object* v_res_1769_; 
v_i_boxed_1767_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_stop_boxed_1768_ = lean_unbox_usize(v_stop_1765_);
lean_dec(v_stop_1765_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2(v_as_1763_, v_i_boxed_1767_, v_stop_boxed_1768_, v_b_1766_);
lean_dec_ref(v_as_1763_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object* v_as_1772_, lean_object* v_start_1773_, lean_object* v_stop_1774_){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___closed__0));
v___x_1776_ = lean_nat_dec_lt(v_start_1773_, v_stop_1774_);
if (v___x_1776_ == 0)
{
return v___x_1775_;
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_array_get_size(v_as_1772_);
v___x_1778_ = lean_nat_dec_le(v_stop_1774_, v___x_1777_);
if (v___x_1778_ == 0)
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_lt(v_start_1773_, v___x_1777_);
if (v___x_1779_ == 0)
{
return v___x_1775_;
}
else
{
size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_usize_of_nat(v_start_1773_);
v___x_1781_ = lean_usize_of_nat(v___x_1777_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2(v_as_1772_, v___x_1780_, v___x_1781_, v___x_1775_);
return v___x_1782_;
}
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_usize_of_nat(v_start_1773_);
v___x_1784_ = lean_usize_of_nat(v_stop_1774_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2_spec__2(v_as_1772_, v___x_1783_, v___x_1784_, v___x_1775_);
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object* v_as_1786_, lean_object* v_start_1787_, lean_object* v_stop_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(v_as_1786_, v_start_1787_, v_stop_1788_);
lean_dec(v_stop_1788_);
lean_dec(v_start_1787_);
lean_dec_ref(v_as_1786_);
return v_res_1789_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_unsigned_to_nat(16u);
v___x_1792_ = lean_mk_array(v___x_1791_, v___x_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
lean_ctor_set(v___x_1801_, 2, v___x_1799_);
lean_ctor_set(v___x_1801_, 3, v___x_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object* v_goal_1802_, lean_object* v_ctx_1803_, lean_object* v_scope_1804_, lean_object* v_stepLimit_x3f_1805_, lean_object* v_frameDB_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v_a_1822_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___y_1846_; 
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1);
v___x_1843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1844_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1805_) == 0)
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_box(1);
v___y_1846_ = v___x_1892_;
goto v___jp_1845_;
}
else
{
lean_object* v_val_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_val_1893_ = lean_ctor_get(v_stepLimit_x3f_1805_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_stepLimit_x3f_1805_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v_stepLimit_x3f_1805_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_val_1893_);
lean_dec(v_stepLimit_x3f_1805_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 0);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_val_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v___y_1846_ = v___x_1898_;
goto v___jp_1845_;
}
}
}
v___jp_1818_:
{
lean_object* v_entries_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_entries_1823_ = lean_ctor_get(v___y_1821_, 1);
lean_inc_ref(v_entries_1823_);
lean_dec_ref(v___y_1821_);
v___x_1824_ = lean_array_get_size(v_entries_1823_);
v___x_1825_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(v_entries_1823_, v___x_1817_, v___x_1824_);
lean_dec_ref(v_entries_1823_);
v___x_1826_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1826_, 0, v___y_1819_);
lean_ctor_set(v___x_1826_, 1, v_a_1822_);
lean_ctor_set(v___x_1826_, 2, v___y_1820_);
lean_ctor_set(v___x_1826_, 3, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
v___jp_1828_:
{
if (lean_obj_tag(v___y_1832_) == 0)
{
lean_object* v_a_1833_; 
v_a_1833_ = lean_ctor_get(v___y_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___y_1832_, 1);
v___y_1819_ = v___y_1829_;
v___y_1820_ = v___y_1830_;
v___y_1821_ = v___y_1831_;
v_a_1822_ = v_a_1833_;
goto v___jp_1818_;
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec_ref(v___y_1829_);
v_a_1834_ = lean_ctor_get(v___y_1832_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___y_1832_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___y_1832_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___y_1832_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
v___jp_1845_:
{
lean_object* v_initState_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; 
v_initState_1847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_initState_1847_, 0, v___x_1842_);
lean_ctor_set(v_initState_1847_, 1, v___x_1842_);
lean_ctor_set(v_initState_1847_, 2, v___x_1842_);
lean_ctor_set(v_initState_1847_, 3, v___x_1842_);
lean_ctor_set(v_initState_1847_, 4, v_frameDB_1806_);
lean_ctor_set(v_initState_1847_, 5, v___x_1843_);
lean_ctor_set(v_initState_1847_, 6, v___x_1843_);
lean_ctor_set(v_initState_1847_, 7, v___x_1844_);
lean_ctor_set(v_initState_1847_, 8, v___y_1846_);
lean_ctor_set(v_initState_1847_, 9, v___x_1842_);
v___f_1848_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1848_, 0, v_initState_1847_);
lean_closure_set(v___f_1848_, 1, v_scope_1804_);
lean_closure_set(v___f_1848_, 2, v_goal_1802_);
lean_closure_set(v___f_1848_, 3, v_ctx_1803_);
v___x_1849_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v___f_1848_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v_snd_1851_; lean_object* v_frameDB_1852_; lean_object* v_invariants_1853_; lean_object* v_vcs_1854_; lean_object* v_inlineHandledInvariants_1855_; size_t v_sz_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v_snd_1851_ = lean_ctor_get(v_a_1850_, 1);
lean_inc(v_snd_1851_);
lean_dec(v_a_1850_);
v_frameDB_1852_ = lean_ctor_get(v_snd_1851_, 4);
lean_inc_ref(v_frameDB_1852_);
v_invariants_1853_ = lean_ctor_get(v_snd_1851_, 5);
lean_inc_ref_n(v_invariants_1853_, 2);
v_vcs_1854_ = lean_ctor_get(v_snd_1851_, 6);
lean_inc_ref(v_vcs_1854_);
v_inlineHandledInvariants_1855_ = lean_ctor_get(v_snd_1851_, 9);
lean_inc_ref(v_inlineHandledInvariants_1855_);
lean_dec(v_snd_1851_);
v_sz_1856_ = lean_array_size(v_invariants_1853_);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(v_sz_1856_, v___x_1857_, v_invariants_1853_, v_a_1813_);
if (lean_obj_tag(v___x_1858_) == 0)
{
size_t v_sz_1859_; lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1858_, 1);
v_sz_1859_ = lean_array_size(v_vcs_1854_);
lean_inc_ref(v_vcs_1854_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg(v_sz_1859_, v___x_1857_, v_vcs_1854_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
lean_dec_ref_known(v___x_1860_, 1);
v___x_1861_ = lean_array_get_size(v_vcs_1854_);
v___x_1862_ = lean_nat_dec_lt(v___x_1817_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v_vcs_1854_);
v___y_1819_ = v_invariants_1853_;
v___y_1820_ = v_inlineHandledInvariants_1855_;
v___y_1821_ = v_frameDB_1852_;
v_a_1822_ = v___x_1843_;
goto v___jp_1818_;
}
else
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_le(v___x_1861_, v___x_1861_);
if (v___x_1863_ == 0)
{
if (v___x_1862_ == 0)
{
lean_dec_ref(v_vcs_1854_);
v___y_1819_ = v_invariants_1853_;
v___y_1820_ = v_inlineHandledInvariants_1855_;
v___y_1821_ = v_frameDB_1852_;
v_a_1822_ = v___x_1843_;
goto v___jp_1818_;
}
else
{
size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_usize_of_nat(v___x_1861_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5(v_vcs_1854_, v___x_1857_, v___x_1864_, v___x_1843_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec_ref(v_vcs_1854_);
v___y_1829_ = v_invariants_1853_;
v___y_1830_ = v_inlineHandledInvariants_1855_;
v___y_1831_ = v_frameDB_1852_;
v___y_1832_ = v___x_1865_;
goto v___jp_1828_;
}
}
else
{
size_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_usize_of_nat(v___x_1861_);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__5(v_vcs_1854_, v___x_1857_, v___x_1866_, v___x_1843_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
lean_dec_ref(v_vcs_1854_);
v___y_1829_ = v_invariants_1853_;
v___y_1830_ = v_inlineHandledInvariants_1855_;
v___y_1831_ = v_frameDB_1852_;
v___y_1832_ = v___x_1867_;
goto v___jp_1828_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_inlineHandledInvariants_1855_);
lean_dec_ref(v_vcs_1854_);
lean_dec_ref(v_invariants_1853_);
lean_dec_ref(v_frameDB_1852_);
v_a_1868_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1860_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1860_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_inlineHandledInvariants_1855_);
lean_dec_ref(v_vcs_1854_);
lean_dec_ref(v_invariants_1853_);
lean_dec_ref(v_frameDB_1852_);
v_a_1876_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1858_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1858_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1849_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1849_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object* v_goal_1901_, lean_object* v_ctx_1902_, lean_object* v_scope_1903_, lean_object* v_stepLimit_x3f_1904_, lean_object* v_frameDB_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_goal_1901_, v_ctx_1902_, v_scope_1903_, v_stepLimit_x3f_1904_, v_frameDB_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object* v_mvarId_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_1917_, v___y_1924_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(v_mvarId_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v_mvarId_1929_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object* v_as_1941_, size_t v_sz_1942_, size_t v_i_1943_, lean_object* v_bs_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___redArg(v_sz_1942_, v_i_1943_, v_bs_1944_, v___y_1951_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object* v_as_1956_, lean_object* v_sz_1957_, lean_object* v_i_1958_, lean_object* v_bs_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
size_t v_sz_boxed_1970_; size_t v_i_boxed_1971_; lean_object* v_res_1972_; 
v_sz_boxed_1970_ = lean_unbox_usize(v_sz_1957_);
lean_dec(v_sz_1957_);
v_i_boxed_1971_ = lean_unbox_usize(v_i_1958_);
lean_dec(v_i_1958_);
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_as_1956_, v_sz_boxed_1970_, v_i_boxed_1971_, v_bs_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v_as_1956_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(lean_object* v_as_1973_, size_t v_sz_1974_, size_t v_i_1975_, lean_object* v_bs_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___redArg(v_sz_1974_, v_i_1975_, v_bs_1976_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4___boxed(lean_object* v_as_1988_, lean_object* v_sz_1989_, lean_object* v_i_1990_, lean_object* v_bs_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
size_t v_sz_boxed_2002_; size_t v_i_boxed_2003_; lean_object* v_res_2004_; 
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1989_);
lean_dec(v_sz_1989_);
v_i_boxed_2003_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__4(v_as_1988_, v_sz_boxed_2002_, v_i_boxed_2003_, v_bs_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v_as_1988_);
return v_res_2004_;
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
