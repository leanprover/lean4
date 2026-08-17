// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Driver
// Imports: public import Lean.Elab.Tactic.Meta public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.Solve public import Lean.Meta.Sym.Grind
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__1_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__15_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__17_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renameI"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__19_value),LEAN_SCALAR_PTR_LITERAL(20, 41, 101, 89, 107, 117, 242, 244)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rename_i"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__27_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(lean_object* v_mvarId_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object* v_mvarId_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mvarId_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec(v_mvarId_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(lean_object* v_mvarId_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mvarId_12_, v___y_16_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___boxed(lean_object* v_mvarId_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(v_mvarId_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(lean_object* v_x_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed(lean_object* v_x_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(v_x_32_);
lean_dec(v_x_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_x_35_, lean_object* v_x_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_ks_39_; lean_object* v_vs_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_64_; 
v_ks_39_ = lean_ctor_get(v_x_35_, 0);
v_vs_40_ = lean_ctor_get(v_x_35_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_x_35_);
if (v_isSharedCheck_64_ == 0)
{
v___x_42_ = v_x_35_;
v_isShared_43_ = v_isSharedCheck_64_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_vs_40_);
lean_inc(v_ks_39_);
lean_dec(v_x_35_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_64_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_array_get_size(v_ks_39_);
v___x_45_ = lean_nat_dec_lt(v_x_36_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
lean_dec(v_x_36_);
v___x_46_ = lean_array_push(v_ks_39_, v_x_37_);
v___x_47_ = lean_array_push(v_vs_40_, v_x_38_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_47_);
lean_ctor_set(v___x_42_, 0, v___x_46_);
v___x_49_ = v___x_42_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
else
{
lean_object* v_k_x27_51_; uint8_t v___x_52_; 
v_k_x27_51_ = lean_array_fget_borrowed(v_ks_39_, v_x_36_);
v___x_52_ = l_Lean_instBEqMVarId_beq(v_x_37_, v_k_x27_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_54_; 
if (v_isShared_43_ == 0)
{
v___x_54_ = v___x_42_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_ks_39_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_vs_40_);
v___x_54_ = v_reuseFailAlloc_58_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_x_36_, v___x_55_);
lean_dec(v_x_36_);
v_x_35_ = v___x_54_;
v_x_36_ = v___x_56_;
goto _start;
}
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_59_ = lean_array_fset(v_ks_39_, v_x_36_, v_x_37_);
v___x_60_ = lean_array_fset(v_vs_40_, v_x_36_, v_x_38_);
lean_dec(v_x_36_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_60_);
lean_ctor_set(v___x_42_, 0, v___x_59_);
v___x_62_ = v___x_42_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_n_65_, lean_object* v_k_66_, lean_object* v_v_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_n_65_, v___x_68_, v_k_66_, v_v_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object* v_x_71_, size_t v_x_72_, size_t v_x_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
lean_object* v_es_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_j_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_es_76_ = lean_ctor_get(v_x_71_, 0);
v___x_77_ = ((size_t)31ULL);
v___x_78_ = lean_usize_land(v_x_72_, v___x_77_);
v_j_79_ = lean_usize_to_nat(v___x_78_);
v___x_80_ = lean_array_get_size(v_es_76_);
v___x_81_ = lean_nat_dec_lt(v_j_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_dec(v_j_79_);
lean_dec(v_x_75_);
lean_dec(v_x_74_);
return v_x_71_;
}
else
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_120_; 
lean_inc_ref(v_es_76_);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v_x_71_, 0);
lean_dec(v_unused_121_);
v___x_83_ = v_x_71_;
v_isShared_84_ = v_isSharedCheck_120_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_x_71_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_120_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_v_85_; lean_object* v___x_86_; lean_object* v_xs_x27_87_; lean_object* v___y_89_; 
v_v_85_ = lean_array_fget(v_es_76_, v_j_79_);
v___x_86_ = lean_box(0);
v_xs_x27_87_ = lean_array_fset(v_es_76_, v_j_79_, v___x_86_);
switch(lean_obj_tag(v_v_85_))
{
case 0:
{
lean_object* v_key_94_; lean_object* v_val_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_105_; 
v_key_94_ = lean_ctor_get(v_v_85_, 0);
v_val_95_ = lean_ctor_get(v_v_85_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_v_85_);
if (v_isSharedCheck_105_ == 0)
{
v___x_97_ = v_v_85_;
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_val_95_);
lean_inc(v_key_94_);
lean_dec(v_v_85_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_instBEqMVarId_beq(v_x_74_, v_key_94_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_del_object(v___x_97_);
v___x_100_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_94_, v_val_95_, v_x_74_, v_x_75_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___y_89_ = v___x_101_;
goto v___jp_88_;
}
else
{
lean_object* v___x_103_; 
lean_dec(v_val_95_);
lean_dec(v_key_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v_x_75_);
lean_ctor_set(v___x_97_, 0, v_x_74_);
v___x_103_ = v___x_97_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_x_74_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_x_75_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v___y_89_ = v___x_103_;
goto v___jp_88_;
}
}
}
}
case 1:
{
lean_object* v_node_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_118_; 
v_node_106_ = lean_ctor_get(v_v_85_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_v_85_);
if (v_isSharedCheck_118_ == 0)
{
v___x_108_ = v_v_85_;
v_isShared_109_ = v_isSharedCheck_118_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_node_106_);
lean_dec(v_v_85_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_118_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_110_ = ((size_t)5ULL);
v___x_111_ = lean_usize_shift_right(v_x_72_, v___x_110_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_x_73_, v___x_112_);
v___x_114_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_node_106_, v___x_111_, v___x_113_, v_x_74_, v_x_75_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_114_);
v___x_116_ = v___x_108_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
v___y_89_ = v___x_116_;
goto v___jp_88_;
}
}
}
default: 
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_x_74_);
lean_ctor_set(v___x_119_, 1, v_x_75_);
v___y_89_ = v___x_119_;
goto v___jp_88_;
}
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_array_fset(v_xs_x27_87_, v_j_79_, v___y_89_);
lean_dec(v_j_79_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_90_);
v___x_92_ = v___x_83_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
else
{
lean_object* v_ks_122_; lean_object* v_vs_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_143_; 
v_ks_122_ = lean_ctor_get(v_x_71_, 0);
v_vs_123_ = lean_ctor_get(v_x_71_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_143_ == 0)
{
v___x_125_ = v_x_71_;
v_isShared_126_ = v_isSharedCheck_143_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_vs_123_);
lean_inc(v_ks_122_);
lean_dec(v_x_71_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_143_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_ks_122_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_vs_123_);
v___x_128_ = v_reuseFailAlloc_142_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v_newNode_129_; uint8_t v___y_131_; size_t v___x_137_; uint8_t v___x_138_; 
v_newNode_129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_128_, v_x_74_, v_x_75_);
v___x_137_ = ((size_t)7ULL);
v___x_138_ = lean_usize_dec_le(v___x_137_, v_x_73_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_129_);
v___x_140_ = lean_unsigned_to_nat(4u);
v___x_141_ = lean_nat_dec_lt(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
v___y_131_ = v___x_141_;
goto v___jp_130_;
}
else
{
v___y_131_ = v___x_138_;
goto v___jp_130_;
}
v___jp_130_:
{
if (v___y_131_ == 0)
{
lean_object* v_ks_132_; lean_object* v_vs_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_ks_132_ = lean_ctor_get(v_newNode_129_, 0);
lean_inc_ref(v_ks_132_);
v_vs_133_ = lean_ctor_get(v_newNode_129_, 1);
lean_inc_ref(v_vs_133_);
lean_dec_ref(v_newNode_129_);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_73_, v_ks_132_, v_vs_133_, v___x_134_, v___x_135_);
lean_dec_ref(v_vs_133_);
lean_dec_ref(v_ks_132_);
return v___x_136_;
}
else
{
return v_newNode_129_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t v_depth_144_, lean_object* v_keys_145_, lean_object* v_vals_146_, lean_object* v_i_147_, lean_object* v_entries_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_array_get_size(v_keys_145_);
v___x_150_ = lean_nat_dec_lt(v_i_147_, v___x_149_);
if (v___x_150_ == 0)
{
lean_dec(v_i_147_);
return v_entries_148_;
}
else
{
lean_object* v_k_151_; lean_object* v_v_152_; uint64_t v___x_153_; size_t v_h_154_; size_t v___x_155_; lean_object* v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v_h_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_k_151_ = lean_array_fget_borrowed(v_keys_145_, v_i_147_);
v_v_152_ = lean_array_fget_borrowed(v_vals_146_, v_i_147_);
v___x_153_ = l_Lean_instHashableMVarId_hash(v_k_151_);
v_h_154_ = lean_uint64_to_usize(v___x_153_);
v___x_155_ = ((size_t)5ULL);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_sub(v_depth_144_, v___x_157_);
v___x_159_ = lean_usize_mul(v___x_155_, v___x_158_);
v_h_160_ = lean_usize_shift_right(v_h_154_, v___x_159_);
v___x_161_ = lean_nat_add(v_i_147_, v___x_156_);
lean_dec(v_i_147_);
lean_inc(v_v_152_);
lean_inc(v_k_151_);
v___x_162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_148_, v_h_160_, v_depth_144_, v_k_151_, v_v_152_);
v_i_147_ = v___x_161_;
v_entries_148_ = v___x_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_depth_164_, lean_object* v_keys_165_, lean_object* v_vals_166_, lean_object* v_i_167_, lean_object* v_entries_168_){
_start:
{
size_t v_depth_boxed_169_; lean_object* v_res_170_; 
v_depth_boxed_169_ = lean_unbox_usize(v_depth_164_);
lean_dec(v_depth_164_);
v_res_170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_169_, v_keys_165_, v_vals_166_, v_i_167_, v_entries_168_);
lean_dec_ref(v_vals_166_);
lean_dec_ref(v_keys_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
size_t v_x_16560__boxed_176_; size_t v_x_16561__boxed_177_; lean_object* v_res_178_; 
v_x_16560__boxed_176_ = lean_unbox_usize(v_x_172_);
lean_dec(v_x_172_);
v_x_16561__boxed_177_ = lean_unbox_usize(v_x_173_);
lean_dec(v_x_173_);
v_res_178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_171_, v_x_16560__boxed_176_, v_x_16561__boxed_177_, v_x_174_, v_x_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
uint64_t v___x_182_; size_t v___x_183_; size_t v___x_184_; lean_object* v___x_185_; 
v___x_182_ = l_Lean_instHashableMVarId_hash(v_x_180_);
v___x_183_ = lean_uint64_to_usize(v___x_182_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_179_, v___x_183_, v___x_184_, v_x_180_, v_x_181_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_186_, lean_object* v_val_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v_mctx_191_; lean_object* v_cache_192_; lean_object* v_zetaDeltaFVarIds_193_; lean_object* v_postponed_194_; lean_object* v_diag_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_224_; 
v___x_190_ = lean_st_ref_take(v___y_188_);
v_mctx_191_ = lean_ctor_get(v___x_190_, 0);
v_cache_192_ = lean_ctor_get(v___x_190_, 1);
v_zetaDeltaFVarIds_193_ = lean_ctor_get(v___x_190_, 2);
v_postponed_194_ = lean_ctor_get(v___x_190_, 3);
v_diag_195_ = lean_ctor_get(v___x_190_, 4);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_224_ == 0)
{
v___x_197_ = v___x_190_;
v_isShared_198_ = v_isSharedCheck_224_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_diag_195_);
lean_inc(v_postponed_194_);
lean_inc(v_zetaDeltaFVarIds_193_);
lean_inc(v_cache_192_);
lean_inc(v_mctx_191_);
lean_dec(v___x_190_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_224_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_depth_199_; lean_object* v_levelAssignDepth_200_; lean_object* v_lmvarCounter_201_; lean_object* v_mvarCounter_202_; lean_object* v_lDecls_203_; lean_object* v_decls_204_; lean_object* v_userNames_205_; lean_object* v_lAssignment_206_; lean_object* v_eAssignment_207_; lean_object* v_dAssignment_208_; lean_object* v_instanceTypedMVars_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_223_; 
v_depth_199_ = lean_ctor_get(v_mctx_191_, 0);
v_levelAssignDepth_200_ = lean_ctor_get(v_mctx_191_, 1);
v_lmvarCounter_201_ = lean_ctor_get(v_mctx_191_, 2);
v_mvarCounter_202_ = lean_ctor_get(v_mctx_191_, 3);
v_lDecls_203_ = lean_ctor_get(v_mctx_191_, 4);
v_decls_204_ = lean_ctor_get(v_mctx_191_, 5);
v_userNames_205_ = lean_ctor_get(v_mctx_191_, 6);
v_lAssignment_206_ = lean_ctor_get(v_mctx_191_, 7);
v_eAssignment_207_ = lean_ctor_get(v_mctx_191_, 8);
v_dAssignment_208_ = lean_ctor_get(v_mctx_191_, 9);
v_instanceTypedMVars_209_ = lean_ctor_get(v_mctx_191_, 10);
v_isSharedCheck_223_ = !lean_is_exclusive(v_mctx_191_);
if (v_isSharedCheck_223_ == 0)
{
v___x_211_ = v_mctx_191_;
v_isShared_212_ = v_isSharedCheck_223_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_instanceTypedMVars_209_);
lean_inc(v_dAssignment_208_);
lean_inc(v_eAssignment_207_);
lean_inc(v_lAssignment_206_);
lean_inc(v_userNames_205_);
lean_inc(v_decls_204_);
lean_inc(v_lDecls_203_);
lean_inc(v_mvarCounter_202_);
lean_inc(v_lmvarCounter_201_);
lean_inc(v_levelAssignDepth_200_);
lean_inc(v_depth_199_);
lean_dec(v_mctx_191_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_223_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_207_, v_mvarId_186_, v_val_187_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 8, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_depth_199_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_levelAssignDepth_200_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_lmvarCounter_201_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_mvarCounter_202_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v_lDecls_203_);
lean_ctor_set(v_reuseFailAlloc_222_, 5, v_decls_204_);
lean_ctor_set(v_reuseFailAlloc_222_, 6, v_userNames_205_);
lean_ctor_set(v_reuseFailAlloc_222_, 7, v_lAssignment_206_);
lean_ctor_set(v_reuseFailAlloc_222_, 8, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_222_, 9, v_dAssignment_208_);
lean_ctor_set(v_reuseFailAlloc_222_, 10, v_instanceTypedMVars_209_);
v___x_215_ = v_reuseFailAlloc_222_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_215_);
v___x_217_ = v___x_197_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_cache_192_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_zetaDeltaFVarIds_193_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v_postponed_194_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_diag_195_);
v___x_217_ = v_reuseFailAlloc_221_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_st_ref_put(v___y_188_, v___x_217_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_225_, lean_object* v_val_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_225_, v_val_226_, v___y_227_);
lean_dec(v___y_227_);
return v_res_229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_keys_230_, lean_object* v_i_231_, lean_object* v_k_232_){
_start:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = lean_array_get_size(v_keys_230_);
v___x_234_ = lean_nat_dec_lt(v_i_231_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec(v_i_231_);
return v___x_234_;
}
else
{
lean_object* v_k_x27_235_; uint8_t v___x_236_; 
v_k_x27_235_ = lean_array_fget_borrowed(v_keys_230_, v_i_231_);
v___x_236_ = l_Lean_instBEqMVarId_beq(v_k_232_, v_k_x27_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_i_231_, v___x_237_);
lean_dec(v_i_231_);
v_i_231_ = v___x_238_;
goto _start;
}
else
{
lean_dec(v_i_231_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_keys_240_, lean_object* v_i_241_, lean_object* v_k_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_240_, v_i_241_, v_k_242_);
lean_dec(v_k_242_);
lean_dec_ref(v_keys_240_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_245_, size_t v_x_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v_es_248_; lean_object* v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v_j_252_; lean_object* v___x_253_; 
v_es_248_ = lean_ctor_get(v_x_245_, 0);
v___x_249_ = lean_box(2);
v___x_250_ = ((size_t)31ULL);
v___x_251_ = lean_usize_land(v_x_246_, v___x_250_);
v_j_252_ = lean_usize_to_nat(v___x_251_);
v___x_253_ = lean_array_get_borrowed(v___x_249_, v_es_248_, v_j_252_);
lean_dec(v_j_252_);
switch(lean_obj_tag(v___x_253_))
{
case 0:
{
lean_object* v_key_254_; uint8_t v___x_255_; 
v_key_254_ = lean_ctor_get(v___x_253_, 0);
v___x_255_ = l_Lean_instBEqMVarId_beq(v_x_247_, v_key_254_);
return v___x_255_;
}
case 1:
{
lean_object* v_node_256_; size_t v___x_257_; size_t v___x_258_; 
v_node_256_ = lean_ctor_get(v___x_253_, 0);
v___x_257_ = ((size_t)5ULL);
v___x_258_ = lean_usize_shift_right(v_x_246_, v___x_257_);
v_x_245_ = v_node_256_;
v_x_246_ = v___x_258_;
goto _start;
}
default: 
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
}
else
{
lean_object* v_ks_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_ks_261_ = lean_ctor_get(v_x_245_, 0);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_261_, v___x_262_, v_x_247_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
size_t v_x_16786__boxed_267_; uint8_t v_res_268_; lean_object* v_r_269_; 
v_x_16786__boxed_267_ = lean_unbox_usize(v_x_265_);
lean_dec(v_x_265_);
v_res_268_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_264_, v_x_16786__boxed_267_, v_x_266_);
lean_dec(v_x_266_);
lean_dec_ref(v_x_264_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
uint64_t v___x_272_; size_t v___x_273_; uint8_t v___x_274_; 
v___x_272_ = l_Lean_instHashableMVarId_hash(v_x_271_);
v___x_273_ = lean_uint64_to_usize(v___x_272_);
v___x_274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_270_, v___x_273_, v_x_271_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_275_, v_x_276_);
lean_dec(v_x_276_);
lean_dec_ref(v_x_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v_mctx_283_; lean_object* v_eAssignment_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = lean_st_ref_get(v___y_280_);
v_mctx_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_mctx_283_);
lean_dec(v___x_282_);
v_eAssignment_284_ = lean_ctor_get(v_mctx_283_, 8);
lean_inc_ref(v_eAssignment_284_);
lean_dec_ref(v_mctx_283_);
v___x_285_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_284_, v_mvarId_279_);
lean_dec_ref(v_eAssignment_284_);
v___x_286_ = lean_box(v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec(v_mvarId_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object* v___f_303_, lean_object* v_mv_304_, lean_object* v_val_305_, lean_object* v_tac_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_fileName_360_; lean_object* v_fileMap_361_; lean_object* v_options_362_; lean_object* v_currRecDepth_363_; lean_object* v_maxRecDepth_364_; lean_object* v_ref_365_; lean_object* v_currNamespace_366_; lean_object* v_openDecls_367_; lean_object* v_initHeartbeats_368_; lean_object* v_maxHeartbeats_369_; lean_object* v_quotContext_370_; lean_object* v_currMacroScope_371_; uint8_t v_diag_372_; lean_object* v_cancelTk_x3f_373_; uint8_t v_suppressElabErrors_374_; lean_object* v_inheritedTraceOptions_375_; lean_object* v_keyedConfig_376_; uint8_t v_trackZetaDelta_377_; lean_object* v_zetaDeltaSet_378_; lean_object* v_lctx_379_; lean_object* v_localInstances_380_; lean_object* v_defEqCtx_x3f_381_; lean_object* v_synthPendingDepth_382_; lean_object* v_customCanUnfoldPredicate_x3f_383_; uint8_t v_univApprox_384_; uint8_t v_inTypeClassResolution_385_; uint8_t v_cacheInferType_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v_ref_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_314_ = lean_box(0);
v___x_315_ = lean_box(0);
v___x_316_ = 1;
v___x_320_ = lean_box(1);
v___x_321_ = 0;
v___x_358_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2));
v___x_359_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_359_, 0, v___x_314_);
lean_ctor_set(v___x_359_, 1, v___x_315_);
lean_ctor_set(v___x_359_, 2, v___x_314_);
lean_ctor_set(v___x_359_, 3, v___f_303_);
lean_ctor_set(v___x_359_, 4, v___x_320_);
lean_ctor_set(v___x_359_, 5, v___x_320_);
lean_ctor_set(v___x_359_, 6, v___x_314_);
lean_ctor_set(v___x_359_, 7, v___x_358_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8, v___x_316_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 1, v___x_316_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 2, v___x_316_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 3, v___x_316_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 4, v___x_321_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 5, v___x_321_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 6, v___x_321_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 7, v___x_321_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 8, v___x_316_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 9, v___x_321_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*8 + 10, v___x_316_);
v_fileName_360_ = lean_ctor_get(v___y_311_, 0);
v_fileMap_361_ = lean_ctor_get(v___y_311_, 1);
v_options_362_ = lean_ctor_get(v___y_311_, 2);
v_currRecDepth_363_ = lean_ctor_get(v___y_311_, 3);
v_maxRecDepth_364_ = lean_ctor_get(v___y_311_, 4);
v_ref_365_ = lean_ctor_get(v___y_311_, 5);
v_currNamespace_366_ = lean_ctor_get(v___y_311_, 6);
v_openDecls_367_ = lean_ctor_get(v___y_311_, 7);
v_initHeartbeats_368_ = lean_ctor_get(v___y_311_, 8);
v_maxHeartbeats_369_ = lean_ctor_get(v___y_311_, 9);
v_quotContext_370_ = lean_ctor_get(v___y_311_, 10);
v_currMacroScope_371_ = lean_ctor_get(v___y_311_, 11);
v_diag_372_ = lean_ctor_get_uint8(v___y_311_, sizeof(void*)*14);
v_cancelTk_x3f_373_ = lean_ctor_get(v___y_311_, 12);
v_suppressElabErrors_374_ = lean_ctor_get_uint8(v___y_311_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_375_ = lean_ctor_get(v___y_311_, 13);
v_keyedConfig_376_ = lean_ctor_get(v___y_309_, 0);
v_trackZetaDelta_377_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*7);
v_zetaDeltaSet_378_ = lean_ctor_get(v___y_309_, 1);
v_lctx_379_ = lean_ctor_get(v___y_309_, 2);
v_localInstances_380_ = lean_ctor_get(v___y_309_, 3);
v_defEqCtx_x3f_381_ = lean_ctor_get(v___y_309_, 4);
v_synthPendingDepth_382_ = lean_ctor_get(v___y_309_, 5);
v_customCanUnfoldPredicate_x3f_383_ = lean_ctor_get(v___y_309_, 6);
v_univApprox_384_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_385_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*7 + 2);
v_cacheInferType_386_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*7 + 3);
v___x_387_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3));
v___x_388_ = 1;
v_ref_389_ = l_Lean_replaceRef(v_val_305_, v_ref_365_);
lean_inc_ref(v_inheritedTraceOptions_375_);
lean_inc(v_cancelTk_x3f_373_);
lean_inc(v_currMacroScope_371_);
lean_inc(v_quotContext_370_);
lean_inc(v_maxHeartbeats_369_);
lean_inc(v_initHeartbeats_368_);
lean_inc(v_openDecls_367_);
lean_inc(v_currNamespace_366_);
lean_inc(v_maxRecDepth_364_);
lean_inc(v_currRecDepth_363_);
lean_inc_ref(v_options_362_);
lean_inc_ref(v_fileMap_361_);
lean_inc_ref(v_fileName_360_);
v___x_390_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_390_, 0, v_fileName_360_);
lean_ctor_set(v___x_390_, 1, v_fileMap_361_);
lean_ctor_set(v___x_390_, 2, v_options_362_);
lean_ctor_set(v___x_390_, 3, v_currRecDepth_363_);
lean_ctor_set(v___x_390_, 4, v_maxRecDepth_364_);
lean_ctor_set(v___x_390_, 5, v_ref_389_);
lean_ctor_set(v___x_390_, 6, v_currNamespace_366_);
lean_ctor_set(v___x_390_, 7, v_openDecls_367_);
lean_ctor_set(v___x_390_, 8, v_initHeartbeats_368_);
lean_ctor_set(v___x_390_, 9, v_maxHeartbeats_369_);
lean_ctor_set(v___x_390_, 10, v_quotContext_370_);
lean_ctor_set(v___x_390_, 11, v_currMacroScope_371_);
lean_ctor_set(v___x_390_, 12, v_cancelTk_x3f_373_);
lean_ctor_set(v___x_390_, 13, v_inheritedTraceOptions_375_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*14, v_diag_372_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*14 + 1, v_suppressElabErrors_374_);
lean_inc_ref(v_keyedConfig_376_);
v___x_391_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_388_, v_keyedConfig_376_);
lean_inc(v_customCanUnfoldPredicate_x3f_383_);
lean_inc(v_synthPendingDepth_382_);
lean_inc(v_defEqCtx_x3f_381_);
lean_inc_ref(v_localInstances_380_);
lean_inc_ref(v_lctx_379_);
lean_inc(v_zetaDeltaSet_378_);
v___x_392_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_zetaDeltaSet_378_);
lean_ctor_set(v___x_392_, 2, v_lctx_379_);
lean_ctor_set(v___x_392_, 3, v_localInstances_380_);
lean_ctor_set(v___x_392_, 4, v_defEqCtx_x3f_381_);
lean_ctor_set(v___x_392_, 5, v_synthPendingDepth_382_);
lean_ctor_set(v___x_392_, 6, v_customCanUnfoldPredicate_x3f_383_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*7, v_trackZetaDelta_377_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*7 + 1, v_univApprox_384_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*7 + 2, v_inTypeClassResolution_385_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*7 + 3, v_cacheInferType_386_);
lean_inc(v_mv_304_);
v___x_393_ = l_Lean_Elab_runTactic(v_mv_304_, v_tac_306_, v___x_359_, v___x_387_, v___x_392_, v___y_310_, v___x_390_, v___y_312_);
lean_dec_ref_known(v___x_390_, 14);
lean_dec_ref_known(v___x_392_, 7);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_dec_ref_known(v___x_393_, 1);
goto v___jp_322_;
}
else
{
if (lean_obj_tag(v___x_393_) == 0)
{
lean_dec_ref_known(v___x_393_, 1);
goto v___jp_322_;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_mv_304_);
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
v___jp_317_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0));
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
v___jp_322_:
{
lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_357_; 
v___x_323_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mv_304_, v___y_310_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_357_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_357_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_357_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
uint8_t v___x_328_; 
v___x_328_ = lean_unbox(v_a_324_);
lean_dec(v_a_324_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_331_; 
lean_dec(v_mv_304_);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_329_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
else
{
lean_object* v___x_333_; lean_object* v_a_334_; 
lean_del_object(v___x_326_);
v___x_333_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mv_304_, v___y_310_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
if (lean_obj_tag(v_a_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_336_; 
v_val_335_ = lean_ctor_get(v_a_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v_a_334_, 1);
v___x_336_ = l_Lean_Meta_Sym_unfoldReducible(v_val_335_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = l_Lean_Meta_Sym_shareCommon(v_a_337_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v___x_340_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mv_304_, v_a_339_, v___y_310_);
lean_dec_ref(v___x_340_);
goto v___jp_317_;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_mv_304_);
v_a_341_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_338_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_mv_304_);
v_a_349_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_336_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_336_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_dec(v_a_334_);
lean_dec(v_mv_304_);
goto v___jp_317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_402_, lean_object* v_mv_403_, lean_object* v_val_404_, lean_object* v_tac_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_402_, v_mv_403_, v_val_404_, v_tac_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v_val_404_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_414_, lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v_key_417_; lean_object* v_value_418_; lean_object* v_tail_419_; uint8_t v___x_420_; 
v_key_417_ = lean_ctor_get(v_x_415_, 0);
v_value_418_ = lean_ctor_get(v_x_415_, 1);
v_tail_419_ = lean_ctor_get(v_x_415_, 2);
v___x_420_ = lean_nat_dec_eq(v_key_417_, v_a_414_);
if (v___x_420_ == 0)
{
v_x_415_ = v_tail_419_;
goto _start;
}
else
{
lean_object* v___x_422_; 
lean_inc(v_value_418_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_value_418_);
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_423_, v_x_424_);
lean_dec(v_x_424_);
lean_dec(v_a_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_buckets_428_; lean_object* v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; uint64_t v_fold_433_; uint64_t v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_buckets_428_ = lean_ctor_get(v_m_426_, 1);
v___x_429_ = lean_array_get_size(v_buckets_428_);
v___x_430_ = lean_uint64_of_nat(v_a_427_);
v___x_431_ = 32ULL;
v___x_432_ = lean_uint64_shift_right(v___x_430_, v___x_431_);
v_fold_433_ = lean_uint64_xor(v___x_430_, v___x_432_);
v___x_434_ = 16ULL;
v___x_435_ = lean_uint64_shift_right(v_fold_433_, v___x_434_);
v___x_436_ = lean_uint64_xor(v_fold_433_, v___x_435_);
v___x_437_ = lean_uint64_to_usize(v___x_436_);
v___x_438_ = lean_usize_of_nat(v___x_429_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_sub(v___x_438_, v___x_439_);
v___x_441_ = lean_usize_land(v___x_437_, v___x_440_);
v___x_442_ = lean_array_uget_borrowed(v_buckets_428_, v___x_441_);
v___x_443_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_427_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_m_444_);
return v_res_446_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Array_mkArray0(lean_box(0));
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object* v_invariantAlts_511_, lean_object* v_n_512_, lean_object* v_mv_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_528_; lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_511_, v_n_512_);
if (lean_obj_tag(v___x_541_) == 1)
{
lean_object* v_val_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_613_; 
v_val_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_613_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_613_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_val_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_613_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___f_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___f_546_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0));
v___x_547_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5));
lean_inc(v_val_542_);
v___x_548_ = l_Lean_Syntax_isOfKind(v_val_542_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7));
lean_inc(v_val_542_);
v___x_550_ = l_Lean_Syntax_isOfKind(v_val_542_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_val_542_);
lean_dec(v_mv_513_);
v___x_551_ = lean_box(v___x_550_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
lean_ctor_set(v___x_544_, 0, v___x_551_);
v___x_553_ = v___x_544_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = l_Lean_Syntax_getArg(v_val_542_, v___x_555_);
v___x_557_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9));
lean_inc(v___x_556_);
v___x_558_ = l_Lean_Syntax_isOfKind(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec(v___x_556_);
lean_dec(v_val_542_);
lean_dec(v_mv_513_);
v___x_559_ = lean_box(v___x_558_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
lean_ctor_set(v___x_544_, 0, v___x_559_);
v___x_561_ = v___x_544_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_args_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_544_);
v_ref_563_ = lean_ctor_get(v_a_518_, 5);
v___x_564_ = l_Lean_Syntax_getArg(v___x_556_, v___x_555_);
lean_dec(v___x_556_);
v___x_565_ = lean_unsigned_to_nat(3u);
v___x_566_ = l_Lean_Syntax_getArg(v_val_542_, v___x_565_);
v_args_567_ = l_Lean_Syntax_getArgs(v___x_564_);
lean_dec(v___x_564_);
v___x_568_ = l_Lean_SourceInfo_fromRef(v_ref_563_, v___x_548_);
v___x_569_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11));
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_568_, 11);
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_568_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14));
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16));
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18));
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20));
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_568_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22);
v___x_579_ = l_Array_append___redArg(v___x_578_, v_args_567_);
lean_dec_ref(v_args_567_);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v___x_568_);
lean_ctor_set(v___x_580_, 1, v___x_574_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
v___x_581_ = l_Lean_Syntax_node2(v___x_568_, v___x_575_, v___x_577_, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23));
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_568_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_585_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_568_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
v___x_587_ = l_Lean_Syntax_node2(v___x_568_, v___x_585_, v___x_586_, v___x_566_);
v___x_588_ = l_Lean_Syntax_node3(v___x_568_, v___x_574_, v___x_581_, v___x_583_, v___x_587_);
v___x_589_ = l_Lean_Syntax_node1(v___x_568_, v___x_573_, v___x_588_);
v___x_590_ = l_Lean_Syntax_node1(v___x_568_, v___x_572_, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26));
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_568_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_Syntax_node3(v___x_568_, v___x_569_, v___x_571_, v___x_590_, v___x_592_);
v___x_594_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_546_, v_mv_513_, v_val_542_, v___x_593_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_val_542_);
v___y_528_ = v___x_594_;
goto v___jp_527_;
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l_Lean_Syntax_getArg(v_val_542_, v___x_595_);
v___x_597_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28));
v___x_598_ = l_Lean_Syntax_isOfKind(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_601_; 
lean_dec(v_val_542_);
lean_dec(v_mv_513_);
v___x_599_ = lean_box(v___x_598_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 0);
lean_ctor_set(v___x_544_, 0, v___x_599_);
v___x_601_ = v___x_544_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
else
{
lean_object* v_ref_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_del_object(v___x_544_);
v_ref_603_ = lean_ctor_get(v_a_518_, 5);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = l_Lean_Syntax_getArg(v_val_542_, v___x_604_);
v___x_606_ = 0;
v___x_607_ = l_Lean_SourceInfo_fromRef(v_ref_603_, v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_609_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
lean_inc(v___x_607_);
v___x_610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
v___x_611_ = l_Lean_Syntax_node2(v___x_607_, v___x_609_, v___x_610_, v___x_605_);
v___x_612_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_546_, v_mv_513_, v_val_542_, v___x_611_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_val_542_);
v___y_528_ = v___x_612_;
goto v___jp_527_;
}
}
}
}
else
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v___x_541_);
lean_dec(v_mv_513_);
v___x_614_ = 0;
v___x_615_ = lean_box(v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
v___jp_521_:
{
if (v___y_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec_ref(v___y_522_);
v___x_524_ = lean_box(v___y_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___y_522_);
return v___x_526_;
}
}
v___jp_527_:
{
if (lean_obj_tag(v___y_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_a_529_ = lean_ctor_get(v___y_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___y_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v___y_528_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___y_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_a_533_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_a_533_);
lean_dec(v_a_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v_a_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v_a_538_; uint8_t v___x_539_; 
v_a_538_ = lean_ctor_get(v___y_528_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___y_528_, 1);
v___x_539_ = l_Lean_Exception_isInterrupt(v_a_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
lean_inc(v_a_538_);
v___x_540_ = l_Lean_Exception_isRuntime(v_a_538_);
v___y_522_ = v_a_538_;
v___y_523_ = v___x_540_;
goto v___jp_521_;
}
else
{
v___y_522_ = v_a_538_;
v___y_523_ = v___x_539_;
goto v___jp_521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_617_, lean_object* v_n_618_, lean_object* v_mv_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_617_, v_n_618_, v_mv_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_n_618_);
lean_dec_ref(v_invariantAlts_617_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_632_, lean_object* v_m_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(v_00_u03b2_632_, v_m_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_m_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_636_, v___y_640_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_mvarId_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v_mvarId_645_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_654_, lean_object* v_val_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_654_, v_val_655_, v___y_659_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_664_, lean_object* v_val_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_664_, v_val_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_678_, lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_678_, v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec(v_a_679_);
return v_res_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_686_, v_x_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec_ref(v_x_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_692_, v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_696_, lean_object* v_x_697_, size_t v_x_698_, lean_object* v_x_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_697_, v_x_698_, v_x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
size_t v_x_17553__boxed_705_; uint8_t v_res_706_; lean_object* v_r_707_; 
v_x_17553__boxed_705_ = lean_unbox_usize(v_x_703_);
lean_dec(v_x_703_);
v_res_706_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_701_, v_x_702_, v_x_17553__boxed_705_, v_x_704_);
lean_dec(v_x_704_);
lean_dec_ref(v_x_702_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_708_, lean_object* v_x_709_, size_t v_x_710_, size_t v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_709_, v_x_710_, v_x_711_, v_x_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
size_t v_x_17564__boxed_721_; size_t v_x_17565__boxed_722_; lean_object* v_res_723_; 
v_x_17564__boxed_721_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_x_17565__boxed_722_ = lean_unbox_usize(v_x_718_);
lean_dec(v_x_718_);
v_res_723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_715_, v_x_716_, v_x_17564__boxed_721_, v_x_17565__boxed_722_, v_x_719_, v_x_720_);
return v_res_723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_724_, lean_object* v_keys_725_, lean_object* v_vals_726_, lean_object* v_heq_727_, lean_object* v_i_728_, lean_object* v_k_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_725_, v_i_728_, v_k_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_731_, lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_heq_734_, lean_object* v_i_735_, lean_object* v_k_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_731_, v_keys_732_, v_vals_733_, v_heq_734_, v_i_735_, v_k_736_);
lean_dec(v_k_736_);
lean_dec_ref(v_vals_733_);
lean_dec_ref(v_keys_732_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_739_, lean_object* v_n_740_, lean_object* v_k_741_, lean_object* v_v_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_740_, v_k_741_, v_v_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_744_, size_t v_depth_745_, lean_object* v_keys_746_, lean_object* v_vals_747_, lean_object* v_heq_748_, lean_object* v_i_749_, lean_object* v_entries_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_745_, v_keys_746_, v_vals_747_, v_i_749_, v_entries_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_752_, lean_object* v_depth_753_, lean_object* v_keys_754_, lean_object* v_vals_755_, lean_object* v_heq_756_, lean_object* v_i_757_, lean_object* v_entries_758_){
_start:
{
size_t v_depth_boxed_759_; lean_object* v_res_760_; 
v_depth_boxed_759_ = lean_unbox_usize(v_depth_753_);
lean_dec(v_depth_753_);
v_res_760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_752_, v_depth_boxed_759_, v_keys_754_, v_vals_755_, v_heq_756_, v_i_757_, v_entries_758_);
lean_dec_ref(v_vals_755_);
lean_dec_ref(v_keys_754_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_762_, v_x_763_, v_x_764_, v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
return v_x_767_;
}
else
{
lean_object* v_key_769_; lean_object* v_value_770_; lean_object* v_tail_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_794_; 
v_key_769_ = lean_ctor_get(v_x_768_, 0);
v_value_770_ = lean_ctor_get(v_x_768_, 1);
v_tail_771_ = lean_ctor_get(v_x_768_, 2);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_794_ == 0)
{
v___x_773_ = v_x_768_;
v_isShared_774_ = v_isSharedCheck_794_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_tail_771_);
lean_inc(v_value_770_);
lean_inc(v_key_769_);
lean_dec(v_x_768_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_794_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; uint64_t v___x_776_; uint64_t v___x_777_; uint64_t v___x_778_; uint64_t v_fold_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_775_ = lean_array_get_size(v_x_767_);
v___x_776_ = lean_uint64_of_nat(v_key_769_);
v___x_777_ = 32ULL;
v___x_778_ = lean_uint64_shift_right(v___x_776_, v___x_777_);
v_fold_779_ = lean_uint64_xor(v___x_776_, v___x_778_);
v___x_780_ = 16ULL;
v___x_781_ = lean_uint64_shift_right(v_fold_779_, v___x_780_);
v___x_782_ = lean_uint64_xor(v_fold_779_, v___x_781_);
v___x_783_ = lean_uint64_to_usize(v___x_782_);
v___x_784_ = lean_usize_of_nat(v___x_775_);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_sub(v___x_784_, v___x_785_);
v___x_787_ = lean_usize_land(v___x_783_, v___x_786_);
v___x_788_ = lean_array_uget_borrowed(v_x_767_, v___x_787_);
lean_inc(v___x_788_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 2, v___x_788_);
v___x_790_ = v___x_773_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_key_769_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_value_770_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_788_);
v___x_790_ = v_reuseFailAlloc_793_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_array_uset(v_x_767_, v___x_787_, v___x_790_);
v_x_767_ = v___x_791_;
v_x_768_ = v_tail_771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_795_, lean_object* v_source_796_, lean_object* v_target_797_){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_array_get_size(v_source_796_);
v___x_799_ = lean_nat_dec_lt(v_i_795_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_source_796_);
lean_dec(v_i_795_);
return v_target_797_;
}
else
{
lean_object* v_es_800_; lean_object* v___x_801_; lean_object* v_source_802_; lean_object* v_target_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_es_800_ = lean_array_fget(v_source_796_, v_i_795_);
v___x_801_ = lean_box(0);
v_source_802_ = lean_array_fset(v_source_796_, v_i_795_, v___x_801_);
v_target_803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_797_, v_es_800_);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_nat_add(v_i_795_, v___x_804_);
lean_dec(v_i_795_);
v_i_795_ = v___x_805_;
v_source_796_ = v_source_802_;
v_target_797_ = v_target_803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_nbuckets_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_808_ = lean_array_get_size(v_data_807_);
v___x_809_ = lean_unsigned_to_nat(2u);
v_nbuckets_810_ = lean_nat_mul(v___x_808_, v___x_809_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_box(0);
v___x_813_ = lean_mk_array(v_nbuckets_810_, v___x_812_);
v___x_814_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_811_, v_data_807_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
else
{
lean_object* v_key_818_; lean_object* v_tail_819_; uint8_t v___x_820_; 
v_key_818_ = lean_ctor_get(v_x_816_, 0);
v_tail_819_ = lean_ctor_get(v_x_816_, 2);
v___x_820_ = lean_nat_dec_eq(v_key_818_, v_a_815_);
if (v___x_820_ == 0)
{
v_x_816_ = v_tail_819_;
goto _start;
}
else
{
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_822_, v_x_823_);
lean_dec(v_x_823_);
lean_dec(v_a_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_826_, lean_object* v_a_827_, lean_object* v_b_828_){
_start:
{
lean_object* v_size_829_; lean_object* v_buckets_830_; lean_object* v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v_fold_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; size_t v___x_843_; lean_object* v_bkt_844_; uint8_t v___x_845_; 
v_size_829_ = lean_ctor_get(v_m_826_, 0);
v_buckets_830_ = lean_ctor_get(v_m_826_, 1);
v___x_831_ = lean_array_get_size(v_buckets_830_);
v___x_832_ = lean_uint64_of_nat(v_a_827_);
v___x_833_ = 32ULL;
v___x_834_ = lean_uint64_shift_right(v___x_832_, v___x_833_);
v_fold_835_ = lean_uint64_xor(v___x_832_, v___x_834_);
v___x_836_ = 16ULL;
v___x_837_ = lean_uint64_shift_right(v_fold_835_, v___x_836_);
v___x_838_ = lean_uint64_xor(v_fold_835_, v___x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = lean_usize_of_nat(v___x_831_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_sub(v___x_840_, v___x_841_);
v___x_843_ = lean_usize_land(v___x_839_, v___x_842_);
v_bkt_844_ = lean_array_uget_borrowed(v_buckets_830_, v___x_843_);
v___x_845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_827_, v_bkt_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_866_; 
lean_inc_ref(v_buckets_830_);
lean_inc(v_size_829_);
v_isSharedCheck_866_ = !lean_is_exclusive(v_m_826_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; lean_object* v_unused_868_; 
v_unused_867_ = lean_ctor_get(v_m_826_, 1);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_m_826_, 0);
lean_dec(v_unused_868_);
v___x_847_ = v_m_826_;
v_isShared_848_ = v_isSharedCheck_866_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_m_826_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_866_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v_size_x27_850_; lean_object* v___x_851_; lean_object* v_buckets_x27_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v_size_x27_850_ = lean_nat_add(v_size_829_, v___x_849_);
lean_dec(v_size_829_);
lean_inc(v_bkt_844_);
v___x_851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_851_, 0, v_a_827_);
lean_ctor_set(v___x_851_, 1, v_b_828_);
lean_ctor_set(v___x_851_, 2, v_bkt_844_);
v_buckets_x27_852_ = lean_array_uset(v_buckets_830_, v___x_843_, v___x_851_);
v___x_853_ = lean_unsigned_to_nat(4u);
v___x_854_ = lean_nat_mul(v_size_x27_850_, v___x_853_);
v___x_855_ = lean_unsigned_to_nat(3u);
v___x_856_ = lean_nat_div(v___x_854_, v___x_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_array_get_size(v_buckets_x27_852_);
v___x_858_ = lean_nat_dec_le(v___x_856_, v___x_857_);
lean_dec(v___x_856_);
if (v___x_858_ == 0)
{
lean_object* v_val_859_; lean_object* v___x_861_; 
v_val_859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_852_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_val_859_);
lean_ctor_set(v___x_847_, 0, v_size_x27_850_);
v___x_861_ = v___x_847_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_size_x27_850_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_val_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_864_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_buckets_x27_852_);
lean_ctor_set(v___x_847_, 0, v_size_x27_850_);
v___x_864_ = v___x_847_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_size_x27_850_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_buckets_x27_852_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_dec(v_b_828_);
lean_dec(v_a_827_);
return v_m_826_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_869_, lean_object* v_as_x27_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
if (lean_obj_tag(v_as_x27_870_) == 0)
{
lean_object* v___x_881_; 
lean_dec_ref(v___x_869_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_b_871_);
return v___x_881_;
}
else
{
lean_object* v_head_882_; lean_object* v_tail_883_; lean_object* v___x_884_; 
v_head_882_ = lean_ctor_get(v_as_x27_870_, 0);
v_tail_883_ = lean_ctor_get(v_as_x27_870_, 1);
lean_inc(v_head_882_);
v___x_884_ = l_Lean_MVarId_getType(v_head_882_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; uint8_t v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
lean_inc_ref(v___x_869_);
v___x_886_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_869_, v_a_885_);
lean_dec(v_a_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_inc(v_head_882_);
v___x_887_ = lean_array_push(v_b_871_, v_head_882_);
v_as_x27_870_ = v_tail_883_;
v_b_871_ = v___x_887_;
goto _start;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_specBackwardRuleCache_891_; lean_object* v_splitBackwardRuleCache_892_; lean_object* v_latticeBackwardRuleCache_893_; lean_object* v_frameBackwardRuleCache_894_; lean_object* v_frameDB_895_; lean_object* v_invariants_896_; lean_object* v_vcs_897_; lean_object* v_simpState_898_; lean_object* v_fuel_899_; lean_object* v_inlineHandledInvariants_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_958_; 
v___x_889_ = lean_st_ref_get(v___y_873_);
v___x_890_ = lean_st_ref_take(v___y_873_);
v_specBackwardRuleCache_891_ = lean_ctor_get(v___x_890_, 0);
v_splitBackwardRuleCache_892_ = lean_ctor_get(v___x_890_, 1);
v_latticeBackwardRuleCache_893_ = lean_ctor_get(v___x_890_, 2);
v_frameBackwardRuleCache_894_ = lean_ctor_get(v___x_890_, 3);
v_frameDB_895_ = lean_ctor_get(v___x_890_, 4);
v_invariants_896_ = lean_ctor_get(v___x_890_, 5);
v_vcs_897_ = lean_ctor_get(v___x_890_, 6);
v_simpState_898_ = lean_ctor_get(v___x_890_, 7);
v_fuel_899_ = lean_ctor_get(v___x_890_, 8);
v_inlineHandledInvariants_900_ = lean_ctor_get(v___x_890_, 9);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_958_ == 0)
{
v___x_902_ = v___x_890_;
v_isShared_903_ = v_isSharedCheck_958_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_inlineHandledInvariants_900_);
lean_inc(v_fuel_899_);
lean_inc(v_simpState_898_);
lean_inc(v_vcs_897_);
lean_inc(v_invariants_896_);
lean_inc(v_frameDB_895_);
lean_inc(v_frameBackwardRuleCache_894_);
lean_inc(v_latticeBackwardRuleCache_893_);
lean_inc(v_splitBackwardRuleCache_892_);
lean_inc(v_specBackwardRuleCache_891_);
lean_dec(v___x_890_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_958_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
lean_inc(v_head_882_);
v___x_904_ = lean_array_push(v_invariants_896_, v_head_882_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 5, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_specBackwardRuleCache_891_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_splitBackwardRuleCache_892_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_latticeBackwardRuleCache_893_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_frameBackwardRuleCache_894_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_frameDB_895_);
lean_ctor_set(v_reuseFailAlloc_957_, 5, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_957_, 6, v_vcs_897_);
lean_ctor_set(v_reuseFailAlloc_957_, 7, v_simpState_898_);
lean_ctor_set(v_reuseFailAlloc_957_, 8, v_fuel_899_);
lean_ctor_set(v_reuseFailAlloc_957_, 9, v_inlineHandledInvariants_900_);
v___x_906_ = v_reuseFailAlloc_957_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v_invariants_908_; lean_object* v_invariantAlts_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_907_ = lean_st_ref_put(v___y_873_, v___x_906_);
v_invariants_908_ = lean_ctor_get(v___x_889_, 5);
lean_inc_ref(v_invariants_908_);
lean_dec(v___x_889_);
v_invariantAlts_909_ = lean_ctor_get(v___y_872_, 3);
v___x_910_ = lean_array_get_size(v_invariants_908_);
lean_dec_ref(v_invariants_908_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v___x_910_, v___x_911_);
lean_inc(v_head_882_);
v___x_913_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_909_, v___x_912_, v_head_882_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; uint8_t v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = lean_unbox(v_a_914_);
lean_dec(v_a_914_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; lean_object* v___x_917_; 
lean_dec(v___x_912_);
v___x_916_ = 2;
lean_inc(v_head_882_);
v___x_917_ = l_Lean_MVarId_setKind___redArg(v_head_882_, v___x_916_, v___y_877_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_dec_ref_known(v___x_917_, 1);
v_as_x27_870_ = v_tail_883_;
goto _start;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_b_871_);
lean_dec_ref(v___x_869_);
v_a_919_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_917_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v___x_927_; lean_object* v_specBackwardRuleCache_928_; lean_object* v_splitBackwardRuleCache_929_; lean_object* v_latticeBackwardRuleCache_930_; lean_object* v_frameBackwardRuleCache_931_; lean_object* v_frameDB_932_; lean_object* v_invariants_933_; lean_object* v_vcs_934_; lean_object* v_simpState_935_; lean_object* v_fuel_936_; lean_object* v_inlineHandledInvariants_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v___x_927_ = lean_st_ref_take(v___y_873_);
v_specBackwardRuleCache_928_ = lean_ctor_get(v___x_927_, 0);
v_splitBackwardRuleCache_929_ = lean_ctor_get(v___x_927_, 1);
v_latticeBackwardRuleCache_930_ = lean_ctor_get(v___x_927_, 2);
v_frameBackwardRuleCache_931_ = lean_ctor_get(v___x_927_, 3);
v_frameDB_932_ = lean_ctor_get(v___x_927_, 4);
v_invariants_933_ = lean_ctor_get(v___x_927_, 5);
v_vcs_934_ = lean_ctor_get(v___x_927_, 6);
v_simpState_935_ = lean_ctor_get(v___x_927_, 7);
v_fuel_936_ = lean_ctor_get(v___x_927_, 8);
v_inlineHandledInvariants_937_ = lean_ctor_get(v___x_927_, 9);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_948_ == 0)
{
v___x_939_ = v___x_927_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_inlineHandledInvariants_937_);
lean_inc(v_fuel_936_);
lean_inc(v_simpState_935_);
lean_inc(v_vcs_934_);
lean_inc(v_invariants_933_);
lean_inc(v_frameDB_932_);
lean_inc(v_frameBackwardRuleCache_931_);
lean_inc(v_latticeBackwardRuleCache_930_);
lean_inc(v_splitBackwardRuleCache_929_);
lean_inc(v_specBackwardRuleCache_928_);
lean_dec(v___x_927_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_937_, v___x_912_, v___x_941_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 9, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_specBackwardRuleCache_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_splitBackwardRuleCache_929_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_latticeBackwardRuleCache_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_frameBackwardRuleCache_931_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_frameDB_932_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v_invariants_933_);
lean_ctor_set(v_reuseFailAlloc_947_, 6, v_vcs_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 7, v_simpState_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 8, v_fuel_936_);
lean_ctor_set(v_reuseFailAlloc_947_, 9, v___x_942_);
v___x_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; 
v___x_945_ = lean_st_ref_put(v___y_873_, v___x_944_);
v_as_x27_870_ = v_tail_883_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v___x_912_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v___x_869_);
v_a_949_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_913_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_913_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v_b_871_);
lean_dec_ref(v___x_869_);
v_a_959_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_884_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_884_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_967_, lean_object* v_as_x27_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_967_, v_as_x27_968_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_as_x27_968_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_env_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = lean_st_ref_get(v_a_993_);
v_env_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_996_);
lean_dec(v___x_995_);
v___x_997_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_998_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_996_, v_subgoals_982_, v___x_997_, v_a_983_, v_a_984_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_subgoals_999_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1013_, lean_object* v_m_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1014_, v_a_1015_, v_b_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1018_, lean_object* v_as_1019_, lean_object* v_as_x27_1020_, lean_object* v_b_1021_, lean_object* v_a_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1018_, v_as_x27_1020_, v_b_1021_, v___y_1023_, v___y_1024_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1036_ = _args[0];
lean_object* v_as_1037_ = _args[1];
lean_object* v_as_x27_1038_ = _args[2];
lean_object* v_b_1039_ = _args[3];
lean_object* v_a_1040_ = _args[4];
lean_object* v___y_1041_ = _args[5];
lean_object* v___y_1042_ = _args[6];
lean_object* v___y_1043_ = _args[7];
lean_object* v___y_1044_ = _args[8];
lean_object* v___y_1045_ = _args[9];
lean_object* v___y_1046_ = _args[10];
lean_object* v___y_1047_ = _args[11];
lean_object* v___y_1048_ = _args[12];
lean_object* v___y_1049_ = _args[13];
lean_object* v___y_1050_ = _args[14];
lean_object* v___y_1051_ = _args[15];
lean_object* v___y_1052_ = _args[16];
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(v___x_1036_, v_as_1037_, v_as_x27_1038_, v_b_1039_, v_a_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v_as_x27_1038_);
lean_dec(v_as_1037_);
return v_res_1053_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1054_, lean_object* v_a_1055_, lean_object* v_x_1056_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1058_, v_a_1059_, v_x_1060_);
lean_dec(v_x_1060_);
lean_dec(v_a_1059_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1063_, lean_object* v_data_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1066_, lean_object* v_i_1067_, lean_object* v_source_1068_, lean_object* v_target_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1067_, v_source_1068_, v_target_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_toGoalState_1088_; lean_object* v_mvarId_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1189_; 
v_toGoalState_1088_ = lean_ctor_get(v_goal_1075_, 0);
v_mvarId_1089_ = lean_ctor_get(v_goal_1075_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_goal_1075_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1091_ = v_goal_1075_;
v_isShared_1092_ = v_isSharedCheck_1189_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_mvarId_1089_);
lean_inc(v_toGoalState_1088_);
lean_dec(v_goal_1075_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1189_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1089_, v_a_1076_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_a_1094_);
v___x_1096_ = v___x_1091_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_toGoalState_1088_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_a_1094_);
v___x_1096_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v___x_1096_, v_a_1076_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1171_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1171_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1171_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_toGoalState_1102_; lean_object* v_mvarId_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1170_; 
v_toGoalState_1102_ = lean_ctor_get(v_a_1098_, 0);
v_mvarId_1103_ = lean_ctor_get(v_a_1098_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_1098_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1105_ = v_a_1098_;
v_isShared_1106_ = v_isSharedCheck_1170_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_mvarId_1103_);
lean_inc(v_toGoalState_1102_);
lean_dec(v_a_1098_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1170_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_mvarId_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; uint8_t v_inconsistent_1145_; 
v_inconsistent_1145_ = lean_ctor_get_uint8(v_toGoalState_1102_, sizeof(void*)*17);
if (v_inconsistent_1145_ == 0)
{
uint8_t v_trivial_1146_; 
lean_del_object(v___x_1100_);
v_trivial_1146_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*5);
if (v_trivial_1146_ == 0)
{
v_mvarId_1108_ = v_mvarId_1103_;
v___y_1109_ = v_a_1077_;
v___y_1110_ = v_a_1084_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Elab_Tactic_VCGen_solveTrivialConjuncts(v_mvarId_1103_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1157_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
if (lean_obj_tag(v_a_1148_) == 1)
{
lean_object* v_val_1152_; 
lean_del_object(v___x_1150_);
v_val_1152_ = lean_ctor_get(v_a_1148_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_a_1148_, 1);
v_mvarId_1108_ = v_val_1152_;
v___y_1109_ = v_a_1077_;
v___y_1110_ = v_a_1084_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v_a_1148_);
lean_del_object(v___x_1105_);
lean_dec_ref(v_toGoalState_1102_);
v___x_1153_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_del_object(v___x_1105_);
lean_dec_ref(v_toGoalState_1102_);
v_a_1158_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1147_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1147_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_del_object(v___x_1105_);
lean_dec(v_mvarId_1103_);
lean_dec_ref(v_toGoalState_1102_);
v___x_1166_ = lean_box(0);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1166_);
v___x_1168_ = v___x_1100_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
v___jp_1107_:
{
uint8_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = 2;
lean_inc(v_mvarId_1108_);
v___x_1112_ = l_Lean_MVarId_setKind___redArg(v_mvarId_1108_, v___x_1111_, v___y_1110_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1112_, 0);
lean_dec(v_unused_1144_);
v___x_1114_ = v___x_1112_;
v_isShared_1115_ = v_isSharedCheck_1143_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v___x_1112_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1143_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v_specBackwardRuleCache_1117_; lean_object* v_splitBackwardRuleCache_1118_; lean_object* v_latticeBackwardRuleCache_1119_; lean_object* v_frameBackwardRuleCache_1120_; lean_object* v_frameDB_1121_; lean_object* v_invariants_1122_; lean_object* v_vcs_1123_; lean_object* v_simpState_1124_; lean_object* v_fuel_1125_; lean_object* v_inlineHandledInvariants_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1142_; 
v___x_1116_ = lean_st_ref_take(v___y_1109_);
v_specBackwardRuleCache_1117_ = lean_ctor_get(v___x_1116_, 0);
v_splitBackwardRuleCache_1118_ = lean_ctor_get(v___x_1116_, 1);
v_latticeBackwardRuleCache_1119_ = lean_ctor_get(v___x_1116_, 2);
v_frameBackwardRuleCache_1120_ = lean_ctor_get(v___x_1116_, 3);
v_frameDB_1121_ = lean_ctor_get(v___x_1116_, 4);
v_invariants_1122_ = lean_ctor_get(v___x_1116_, 5);
v_vcs_1123_ = lean_ctor_get(v___x_1116_, 6);
v_simpState_1124_ = lean_ctor_get(v___x_1116_, 7);
v_fuel_1125_ = lean_ctor_get(v___x_1116_, 8);
v_inlineHandledInvariants_1126_ = lean_ctor_get(v___x_1116_, 9);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1128_ = v___x_1116_;
v_isShared_1129_ = v_isSharedCheck_1142_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_inlineHandledInvariants_1126_);
lean_inc(v_fuel_1125_);
lean_inc(v_simpState_1124_);
lean_inc(v_vcs_1123_);
lean_inc(v_invariants_1122_);
lean_inc(v_frameDB_1121_);
lean_inc(v_frameBackwardRuleCache_1120_);
lean_inc(v_latticeBackwardRuleCache_1119_);
lean_inc(v_splitBackwardRuleCache_1118_);
lean_inc(v_specBackwardRuleCache_1117_);
lean_dec(v___x_1116_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1142_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v_mvarId_1108_);
v___x_1131_ = v___x_1105_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_toGoalState_1102_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_mvarId_1108_);
v___x_1131_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_array_push(v_vcs_1123_, v___x_1131_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 6, v___x_1132_);
v___x_1134_ = v___x_1128_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_specBackwardRuleCache_1117_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_splitBackwardRuleCache_1118_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_latticeBackwardRuleCache_1119_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_frameBackwardRuleCache_1120_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_frameDB_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_invariants_1122_);
lean_ctor_set(v_reuseFailAlloc_1140_, 6, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1140_, 7, v_simpState_1124_);
lean_ctor_set(v_reuseFailAlloc_1140_, 8, v_fuel_1125_);
lean_ctor_set(v_reuseFailAlloc_1140_, 9, v_inlineHandledInvariants_1126_);
v___x_1134_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = lean_st_ref_put(v___y_1109_, v___x_1134_);
v___x_1136_ = lean_box(0);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1136_);
v___x_1138_ = v___x_1114_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
else
{
lean_dec(v_mvarId_1108_);
lean_del_object(v___x_1105_);
lean_dec_ref(v_toGoalState_1102_);
return v___x_1112_;
}
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
v_a_1172_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1097_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1097_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_del_object(v___x_1091_);
lean_dec_ref(v_toGoalState_1088_);
v_a_1181_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1093_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1093_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object* v_mvarId_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v_mctx_1208_; lean_object* v_eAssignment_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1207_ = lean_st_ref_get(v___y_1205_);
v_mctx_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc_ref(v_mctx_1208_);
lean_dec(v___x_1207_);
v_eAssignment_1209_ = lean_ctor_get(v_mctx_1208_, 8);
lean_inc_ref(v_eAssignment_1209_);
lean_dec_ref(v_mctx_1208_);
v___x_1210_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1209_, v_mvarId_1204_);
lean_dec_ref(v_eAssignment_1209_);
v___x_1211_ = lean_box(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object* v_mvarId_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec(v_mvarId_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v___x_1217_, lean_object* v_scope_1218_, size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_bs_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1222_ == 0)
{
lean_dec_ref(v_scope_1218_);
lean_dec_ref(v___x_1217_);
return v_bs_1221_;
}
else
{
lean_object* v_v_1223_; lean_object* v___x_1224_; lean_object* v_bs_x27_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_v_1223_ = lean_array_uget(v_bs_1221_, v_i_1220_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v_bs_x27_1225_ = lean_array_uset(v_bs_1221_, v_i_1220_, v___x_1224_);
lean_inc_ref(v___x_1217_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1217_);
lean_ctor_set(v___x_1226_, 1, v_v_1223_);
lean_inc_ref(v_scope_1218_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_scope_1218_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1220_, v___x_1228_);
v___x_1230_ = lean_array_uset(v_bs_x27_1225_, v_i_1220_, v___x_1227_);
v_i_1220_ = v___x_1229_;
v_bs_1221_ = v___x_1230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v___x_1232_, lean_object* v_scope_1233_, lean_object* v_sz_1234_, lean_object* v_i_1235_, lean_object* v_bs_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1234_);
lean_dec(v_sz_1234_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v___x_1232_, v_scope_1233_, v_sz_boxed_1237_, v_i_boxed_1238_, v_bs_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1253_ = lean_array_get_size(v_a_1240_);
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_sub(v___x_1253_, v___x_1254_);
v___x_1256_ = lean_nat_dec_lt(v___x_1255_, v___x_1253_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_dec(v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1240_);
return v___x_1257_;
}
else
{
lean_object* v___x_1258_; lean_object* v_goal_1259_; lean_object* v_scope_1260_; lean_object* v_mvarId_1261_; lean_object* v___x_1262_; 
v___x_1258_ = lean_array_fget_borrowed(v_a_1240_, v___x_1255_);
lean_dec(v___x_1255_);
v_goal_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_ref(v_goal_1259_);
v_scope_1260_ = lean_ctor_get(v___x_1258_, 1);
lean_inc_ref(v_scope_1260_);
v_mvarId_1261_ = lean_ctor_get(v_goal_1259_, 1);
v___x_1262_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1261_, v___y_1249_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_array_pop(v_a_1240_);
v___x_1265_ = lean_unbox(v_a_1263_);
lean_dec(v_a_1263_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1259_, v___y_1241_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_toGoalState_1268_; uint8_t v_inconsistent_1269_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_toGoalState_1268_ = lean_ctor_get(v_a_1267_, 0);
v_inconsistent_1269_ = lean_ctor_get_uint8(v_toGoalState_1268_, sizeof(void*)*17);
if (v_inconsistent_1269_ == 0)
{
lean_object* v_mvarId_1270_; lean_object* v___x_1271_; 
v_mvarId_1270_ = lean_ctor_get(v_a_1267_, 1);
lean_inc(v_mvarId_1270_);
v___x_1271_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1260_, v_mvarId_1270_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
if (lean_obj_tag(v_a_1272_) == 0)
{
lean_object* v_scope_1273_; lean_object* v_subgoals_1274_; lean_object* v___x_1275_; 
lean_inc_ref(v_toGoalState_1268_);
lean_dec(v_a_1267_);
v_scope_1273_ = lean_ctor_get(v_a_1272_, 0);
lean_inc_ref(v_scope_1273_);
v_subgoals_1274_ = lean_ctor_get(v_a_1272_, 1);
lean_inc(v_subgoals_1274_);
lean_dec_ref_known(v_a_1272_, 2);
v___x_1275_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1274_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v_subgoals_1274_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; size_t v_sz_1278_; size_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = l_Array_reverse___redArg(v_a_1276_);
v_sz_1278_ = lean_array_size(v___x_1277_);
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_toGoalState_1268_, v_scope_1273_, v_sz_1278_, v___x_1279_, v___x_1277_);
v___x_1281_ = l_Array_append___redArg(v___x_1264_, v___x_1280_);
lean_dec_ref(v___x_1280_);
v_a_1240_ = v___x_1281_;
goto _start;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_scope_1273_);
lean_dec_ref(v_toGoalState_1268_);
lean_dec_ref(v___x_1264_);
v_a_1283_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1275_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1275_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v___x_1291_; 
lean_dec_ref_known(v_a_1272_, 1);
v___x_1291_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1267_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_dec_ref_known(v___x_1291_, 1);
v_a_1240_ = v___x_1264_;
goto _start;
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v___x_1264_);
v_a_1293_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1291_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1291_);
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
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_a_1267_);
lean_dec_ref(v___x_1264_);
v_a_1301_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1271_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1271_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_dec(v_a_1267_);
lean_dec_ref(v_scope_1260_);
v_a_1240_ = v___x_1264_;
goto _start;
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v___x_1264_);
lean_dec_ref(v_scope_1260_);
v_a_1310_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1266_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1266_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1260_);
lean_dec_ref(v_goal_1259_);
v_a_1240_ = v___x_1264_;
goto _start;
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_scope_1260_);
lean_dec_ref(v_goal_1259_);
lean_dec_ref(v_a_1240_);
v_a_1319_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1262_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1262_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_a_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1341_, lean_object* v_goal_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_toGoalState_1355_; lean_object* v_mvarId_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1395_; 
v_toGoalState_1355_ = lean_ctor_get(v_goal_1342_, 0);
v_mvarId_1356_ = lean_ctor_get(v_goal_1342_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_goal_1342_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1358_ = v_goal_1342_;
v_isShared_1359_ = v_isSharedCheck_1395_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_mvarId_1356_);
lean_inc(v_toGoalState_1355_);
lean_dec(v_goal_1342_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1395_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1356_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_a_1361_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_toGoalState_1355_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_a_1361_);
v___x_1363_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v_scope_1341_);
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_mk_empty_array_with_capacity(v___x_1365_);
v___x_1367_ = lean_array_push(v___x_1366_, v___x_1364_);
v___x_1368_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v___x_1367_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1368_, 0);
lean_dec(v_unused_1377_);
v___x_1370_ = v___x_1368_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v___x_1368_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = lean_box(0);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1368_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1368_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_del_object(v___x_1358_);
lean_dec_ref(v_toGoalState_1355_);
lean_dec_ref(v_scope_1341_);
v_a_1387_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1360_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1360_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1396_, lean_object* v_goal_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1396_, v_goal_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v_mvarId_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1411_, v___y_1420_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v_mvarId_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_mvarId_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v_mvarId_1425_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_inst_1439_, lean_object* v_a_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_inst_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_inst_1454_, v_a_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_config_1480_; lean_object* v_sharedExprs_1481_; uint8_t v_verbose_1482_; uint8_t v_enforceUnfoldReducible_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_config_1480_ = lean_ctor_get(v___y_1473_, 1);
v_sharedExprs_1481_ = lean_ctor_get(v___y_1473_, 0);
v_verbose_1482_ = lean_ctor_get_uint8(v_config_1480_, 0);
v_enforceUnfoldReducible_1483_ = lean_ctor_get_uint8(v_config_1480_, 1);
v___x_1484_ = 0;
v___x_1485_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_1485_, 0, v_verbose_1482_);
lean_ctor_set_uint8(v___x_1485_, 1, v_enforceUnfoldReducible_1483_);
lean_ctor_set_uint8(v___x_1485_, 2, v___x_1484_);
lean_inc_ref(v_sharedExprs_1481_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_sharedExprs_1481_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1476_);
lean_inc_ref(v___y_1475_);
lean_inc(v___y_1474_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
v___x_1487_ = lean_apply_10(v_x_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___x_1486_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, lean_box(0));
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_1500_, lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_1526_, lean_object* v_scope_1527_, lean_object* v_goal_1528_, lean_object* v_ctx_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_st_mk_ref(v_initState_1526_);
v___x_1541_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1527_, v_goal_1528_, v_ctx_1529_, v___x_1540_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1551_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = lean_st_ref_get(v___x_1540_);
lean_dec(v___x_1540_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1542_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v___x_1540_);
v_a_1552_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1541_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1541_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_1560_, lean_object* v_scope_1561_, lean_object* v_goal_1562_, lean_object* v_ctx_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_1560_, v_scope_1561_, v_goal_1562_, v_ctx_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v_ctx_1563_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v_mctx_1579_; lean_object* v_eAssignment_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = lean_st_ref_get(v___y_1576_);
v_mctx_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_ref(v_mctx_1579_);
lean_dec(v___x_1578_);
v_eAssignment_1580_ = lean_ctor_get(v_mctx_1579_, 8);
lean_inc_ref(v_eAssignment_1580_);
lean_dec_ref(v_mctx_1579_);
v___x_1581_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1580_, v_mvarId_1575_);
lean_dec_ref(v_eAssignment_1580_);
v___x_1582_ = lean_box(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec(v_mvarId_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_1588_, size_t v_i_1589_, size_t v_stop_1590_, lean_object* v_b_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_a_1603_; uint8_t v___x_1607_; 
v___x_1607_ = lean_usize_dec_eq(v_i_1589_, v_stop_1590_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v_mvarId_1611_; lean_object* v___x_1612_; 
v___x_1608_ = lean_array_uget_borrowed(v_as_1588_, v_i_1589_);
v_mvarId_1611_ = lean_ctor_get(v___x_1608_, 1);
v___x_1612_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1611_, v___y_1598_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; uint8_t v___x_1614_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_unbox(v_a_1613_);
lean_dec(v_a_1613_);
if (v___x_1614_ == 0)
{
goto v___jp_1609_;
}
else
{
v_a_1603_ = v_b_1591_;
goto v___jp_1602_;
}
}
else
{
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1615_; uint8_t v___x_1616_; 
v_a_1615_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1616_ = lean_unbox(v_a_1615_);
lean_dec(v_a_1615_);
if (v___x_1616_ == 0)
{
v_a_1603_ = v_b_1591_;
goto v___jp_1602_;
}
else
{
goto v___jp_1609_;
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_b_1591_);
v_a_1617_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1612_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1612_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v___jp_1609_:
{
lean_object* v___x_1610_; 
lean_inc(v___x_1608_);
v___x_1610_ = lean_array_push(v_b_1591_, v___x_1608_);
v_a_1603_ = v___x_1610_;
goto v___jp_1602_;
}
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_b_1591_);
return v___x_1625_;
}
v___jp_1602_:
{
size_t v___x_1604_; size_t v___x_1605_; 
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_add(v_i_1589_, v___x_1604_);
v_i_1589_ = v___x_1605_;
v_b_1591_ = v_a_1603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_stop_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
size_t v_i_boxed_1640_; size_t v_stop_boxed_1641_; lean_object* v_res_1642_; 
v_i_boxed_1640_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v_stop_boxed_1641_ = lean_unbox_usize(v_stop_1628_);
lean_dec(v_stop_1628_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_1626_, v_i_boxed_1640_, v_stop_boxed_1641_, v_b_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v_as_1626_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_1644_, size_t v_i_1645_, lean_object* v_bs_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_usize_dec_lt(v_i_1645_, v_sz_1644_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_bs_1646_);
return v___x_1653_;
}
else
{
lean_object* v_v_1654_; lean_object* v_mvarId_1655_; lean_object* v___x_1656_; 
v_v_1654_ = lean_array_uget_borrowed(v_bs_1646_, v_i_1645_);
v_mvarId_1655_ = lean_ctor_get(v_v_1654_, 1);
lean_inc_n(v_mvarId_1655_, 2);
v___x_1656_ = l_Lean_MVarId_getTag(v_mvarId_1655_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; lean_object* v_bs_x27_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = lean_unsigned_to_nat(0u);
v_bs_x27_1659_ = lean_array_uset(v_bs_1646_, v_i_1645_, v___x_1658_);
v___x_1660_ = lean_usize_to_nat(v_i_1645_);
v___x_1661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_nat_add(v___x_1660_, v___x_1662_);
lean_dec(v___x_1660_);
v___x_1664_ = l_Nat_reprFast(v___x_1663_);
v___x_1665_ = lean_string_append(v___x_1661_, v___x_1664_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = lean_box(0);
v___x_1667_ = l_Lean_Name_str___override(v___x_1666_, v___x_1665_);
v___x_1668_ = l_Lean_Name_eraseMacroScopes(v_a_1657_);
lean_dec(v_a_1657_);
v___x_1669_ = l_Lean_Name_append(v___x_1667_, v___x_1668_);
v___x_1670_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1655_, v___x_1669_, v___y_1648_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; size_t v___x_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1645_, v___x_1672_);
v___x_1674_ = lean_array_uset(v_bs_x27_1659_, v_i_1645_, v_a_1671_);
v_i_1645_ = v___x_1673_;
v_bs_1646_ = v___x_1674_;
goto _start;
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_bs_x27_1659_);
v_a_1676_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1670_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1670_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_mvarId_1655_);
lean_dec_ref(v_bs_1646_);
v_a_1684_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1656_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1656_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_1692_, lean_object* v_i_1693_, lean_object* v_bs_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1692_);
lean_dec(v_sz_1692_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1693_);
lean_dec(v_i_1693_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_1700_, v_i_boxed_1701_, v_bs_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_1704_, size_t v_i_1705_, lean_object* v_bs_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_bs_1706_);
return v___x_1710_;
}
else
{
lean_object* v_v_1711_; lean_object* v___x_1712_; lean_object* v_bs_x27_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_v_1711_ = lean_array_uget(v_bs_1706_, v_i_1705_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v_bs_x27_1713_ = lean_array_uset(v_bs_1706_, v_i_1705_, v___x_1712_);
v___x_1714_ = lean_usize_to_nat(v_i_1705_);
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v___x_1714_, v___x_1716_);
lean_dec(v___x_1714_);
v___x_1718_ = l_Nat_reprFast(v___x_1717_);
v___x_1719_ = lean_string_append(v___x_1715_, v___x_1718_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Lean_Name_str___override(v___x_1720_, v___x_1719_);
v___x_1722_ = l_Lean_MVarId_setTag___redArg(v_v_1711_, v___x_1721_, v___y_1707_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_i_1705_, v___x_1724_);
v___x_1726_ = lean_array_uset(v_bs_x27_1713_, v_i_1705_, v_a_1723_);
v_i_1705_ = v___x_1725_;
v_bs_1706_ = v___x_1726_;
goto _start;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v_bs_x27_1713_);
v_a_1728_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1722_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1722_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1736_, lean_object* v_i_1737_, lean_object* v_bs_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
size_t v_sz_boxed_1741_; size_t v_i_boxed_1742_; lean_object* v_res_1743_; 
v_sz_boxed_1741_ = lean_unbox_usize(v_sz_1736_);
lean_dec(v_sz_1736_);
v_i_boxed_1742_ = lean_unbox_usize(v_i_1737_);
lean_dec(v_i_1737_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_1741_, v_i_boxed_1742_, v_bs_1738_, v___y_1739_);
lean_dec(v___y_1739_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_1744_, size_t v_i_1745_, size_t v_stop_1746_, lean_object* v_b_1747_){
_start:
{
lean_object* v___y_1749_; uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_eq(v_i_1745_, v_stop_1746_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; uint8_t v_retired_1755_; 
v___x_1754_ = lean_array_uget_borrowed(v_as_1744_, v_i_1745_);
v_retired_1755_ = lean_ctor_get_uint8(v___x_1754_, sizeof(void*)*4);
if (v_retired_1755_ == 0)
{
lean_object* v_frameStx_1756_; lean_object* v___x_1757_; 
v_frameStx_1756_ = lean_ctor_get(v___x_1754_, 2);
lean_inc(v_frameStx_1756_);
v___x_1757_ = lean_array_push(v_b_1747_, v_frameStx_1756_);
v___y_1749_ = v___x_1757_;
goto v___jp_1748_;
}
else
{
v___y_1749_ = v_b_1747_;
goto v___jp_1748_;
}
}
else
{
return v_b_1747_;
}
v___jp_1748_:
{
size_t v___x_1750_; size_t v___x_1751_; 
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1745_, v___x_1750_);
v_i_1745_ = v___x_1751_;
v_b_1747_ = v___y_1749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_1758_, lean_object* v_i_1759_, lean_object* v_stop_1760_, lean_object* v_b_1761_){
_start:
{
size_t v_i_boxed_1762_; size_t v_stop_boxed_1763_; lean_object* v_res_1764_; 
v_i_boxed_1762_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_stop_boxed_1763_ = lean_unbox_usize(v_stop_1760_);
lean_dec(v_stop_1760_);
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1758_, v_i_boxed_1762_, v_stop_boxed_1763_, v_b_1761_);
lean_dec_ref(v_as_1758_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_1767_, lean_object* v_start_1768_, lean_object* v_stop_1769_){
_start:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0));
v___x_1771_ = lean_nat_dec_lt(v_start_1768_, v_stop_1769_);
if (v___x_1771_ == 0)
{
return v___x_1770_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_array_get_size(v_as_1767_);
v___x_1773_ = lean_nat_dec_le(v_stop_1769_, v___x_1772_);
if (v___x_1773_ == 0)
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_lt(v_start_1768_, v___x_1772_);
if (v___x_1774_ == 0)
{
return v___x_1770_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_usize_of_nat(v_start_1768_);
v___x_1776_ = lean_usize_of_nat(v___x_1772_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1767_, v___x_1775_, v___x_1776_, v___x_1770_);
return v___x_1777_;
}
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_usize_of_nat(v_start_1768_);
v___x_1779_ = lean_usize_of_nat(v_stop_1769_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1767_, v___x_1778_, v___x_1779_, v___x_1770_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_1781_, lean_object* v_start_1782_, lean_object* v_stop_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_1781_, v_start_1782_, v_stop_1783_);
lean_dec(v_stop_1783_);
lean_dec(v_start_1782_);
lean_dec_ref(v_as_1781_);
return v_res_1784_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_box(0);
v___x_1786_ = lean_unsigned_to_nat(16u);
v___x_1787_ = lean_mk_array(v___x_1786_, v___x_1785_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___x_1794_);
lean_ctor_set(v___x_1796_, 2, v___x_1794_);
lean_ctor_set(v___x_1796_, 3, v___x_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_1797_, lean_object* v_ctx_1798_, lean_object* v_scope_1799_, lean_object* v_stepLimit_x3f_1800_, lean_object* v_frameDB_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v_a_1817_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___y_1841_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_1838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1839_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1800_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_box(1);
v___y_1841_ = v___x_1887_;
goto v___jp_1840_;
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_val_1888_ = lean_ctor_get(v_stepLimit_x3f_1800_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_stepLimit_x3f_1800_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v_stepLimit_x3f_1800_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_val_1888_);
lean_dec(v_stepLimit_x3f_1800_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_val_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
v___y_1841_ = v___x_1893_;
goto v___jp_1840_;
}
}
}
v___jp_1813_:
{
lean_object* v_entries_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_entries_1818_ = lean_ctor_get(v___y_1815_, 1);
lean_inc_ref(v_entries_1818_);
lean_dec_ref(v___y_1815_);
v___x_1819_ = lean_array_get_size(v_entries_1818_);
v___x_1820_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_1818_, v___x_1812_, v___x_1819_);
lean_dec_ref(v_entries_1818_);
v___x_1821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1821_, 0, v___y_1814_);
lean_ctor_set(v___x_1821_, 1, v_a_1817_);
lean_ctor_set(v___x_1821_, 2, v___y_1816_);
lean_ctor_set(v___x_1821_, 3, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
v___jp_1823_:
{
if (lean_obj_tag(v___y_1827_) == 0)
{
lean_object* v_a_1828_; 
v_a_1828_ = lean_ctor_get(v___y_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___y_1827_, 1);
v___y_1814_ = v___y_1824_;
v___y_1815_ = v___y_1825_;
v___y_1816_ = v___y_1826_;
v_a_1817_ = v_a_1828_;
goto v___jp_1813_;
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v___y_1824_);
v_a_1829_ = lean_ctor_get(v___y_1827_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___y_1827_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___y_1827_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___y_1827_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
v___jp_1840_:
{
lean_object* v_initState_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; 
v_initState_1842_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_initState_1842_, 0, v___x_1837_);
lean_ctor_set(v_initState_1842_, 1, v___x_1837_);
lean_ctor_set(v_initState_1842_, 2, v___x_1837_);
lean_ctor_set(v_initState_1842_, 3, v___x_1837_);
lean_ctor_set(v_initState_1842_, 4, v_frameDB_1801_);
lean_ctor_set(v_initState_1842_, 5, v___x_1838_);
lean_ctor_set(v_initState_1842_, 6, v___x_1838_);
lean_ctor_set(v_initState_1842_, 7, v___x_1839_);
lean_ctor_set(v_initState_1842_, 8, v___y_1841_);
lean_ctor_set(v_initState_1842_, 9, v___x_1837_);
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1843_, 0, v_initState_1842_);
lean_closure_set(v___f_1843_, 1, v_scope_1799_);
lean_closure_set(v___f_1843_, 2, v_goal_1797_);
lean_closure_set(v___f_1843_, 3, v_ctx_1798_);
v___x_1844_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_1843_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v_snd_1846_; lean_object* v_frameDB_1847_; lean_object* v_invariants_1848_; lean_object* v_vcs_1849_; lean_object* v_inlineHandledInvariants_1850_; size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v_snd_1846_ = lean_ctor_get(v_a_1845_, 1);
lean_inc(v_snd_1846_);
lean_dec(v_a_1845_);
v_frameDB_1847_ = lean_ctor_get(v_snd_1846_, 4);
lean_inc_ref(v_frameDB_1847_);
v_invariants_1848_ = lean_ctor_get(v_snd_1846_, 5);
lean_inc_ref_n(v_invariants_1848_, 2);
v_vcs_1849_ = lean_ctor_get(v_snd_1846_, 6);
lean_inc_ref(v_vcs_1849_);
v_inlineHandledInvariants_1850_ = lean_ctor_get(v_snd_1846_, 9);
lean_inc_ref(v_inlineHandledInvariants_1850_);
lean_dec(v_snd_1846_);
v_sz_1851_ = lean_array_size(v_invariants_1848_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1851_, v___x_1852_, v_invariants_1848_, v_a_1808_);
if (lean_obj_tag(v___x_1853_) == 0)
{
size_t v_sz_1854_; lean_object* v___x_1855_; 
lean_dec_ref_known(v___x_1853_, 1);
v_sz_1854_ = lean_array_size(v_vcs_1849_);
lean_inc_ref(v_vcs_1849_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1854_, v___x_1852_, v_vcs_1849_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
lean_dec_ref_known(v___x_1855_, 1);
v___x_1856_ = lean_array_get_size(v_vcs_1849_);
v___x_1857_ = lean_nat_dec_lt(v___x_1812_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_vcs_1849_);
v___y_1814_ = v_invariants_1848_;
v___y_1815_ = v_frameDB_1847_;
v___y_1816_ = v_inlineHandledInvariants_1850_;
v_a_1817_ = v___x_1838_;
goto v___jp_1813_;
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_nat_dec_le(v___x_1856_, v___x_1856_);
if (v___x_1858_ == 0)
{
if (v___x_1857_ == 0)
{
lean_dec_ref(v_vcs_1849_);
v___y_1814_ = v_invariants_1848_;
v___y_1815_ = v_frameDB_1847_;
v___y_1816_ = v_inlineHandledInvariants_1850_;
v_a_1817_ = v___x_1838_;
goto v___jp_1813_;
}
else
{
size_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_usize_of_nat(v___x_1856_);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1849_, v___x_1852_, v___x_1859_, v___x_1838_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec_ref(v_vcs_1849_);
v___y_1824_ = v_invariants_1848_;
v___y_1825_ = v_frameDB_1847_;
v___y_1826_ = v_inlineHandledInvariants_1850_;
v___y_1827_ = v___x_1860_;
goto v___jp_1823_;
}
}
else
{
size_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_usize_of_nat(v___x_1856_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1849_, v___x_1852_, v___x_1861_, v___x_1838_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec_ref(v_vcs_1849_);
v___y_1824_ = v_invariants_1848_;
v___y_1825_ = v_frameDB_1847_;
v___y_1826_ = v_inlineHandledInvariants_1850_;
v___y_1827_ = v___x_1862_;
goto v___jp_1823_;
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_inlineHandledInvariants_1850_);
lean_dec_ref(v_vcs_1849_);
lean_dec_ref(v_invariants_1848_);
lean_dec_ref(v_frameDB_1847_);
v_a_1863_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1855_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1855_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_inlineHandledInvariants_1850_);
lean_dec_ref(v_vcs_1849_);
lean_dec_ref(v_invariants_1848_);
lean_dec_ref(v_frameDB_1847_);
v_a_1871_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1853_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1853_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1844_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1844_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_1896_, lean_object* v_ctx_1897_, lean_object* v_scope_1898_, lean_object* v_stepLimit_x3f_1899_, lean_object* v_frameDB_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_1896_, v_ctx_1897_, v_scope_1898_, v_stepLimit_x3f_1899_, v_frameDB_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1912_, v___y_1919_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec(v_mvarId_1924_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_1936_, size_t v_sz_1937_, size_t v_i_1938_, lean_object* v_bs_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1937_, v_i_1938_, v_bs_1939_, v___y_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_1951_, lean_object* v_sz_1952_, lean_object* v_i_1953_, lean_object* v_bs_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
size_t v_sz_boxed_1965_; size_t v_i_boxed_1966_; lean_object* v_res_1967_; 
v_sz_boxed_1965_ = lean_unbox_usize(v_sz_1952_);
lean_dec(v_sz_1952_);
v_i_boxed_1966_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_1951_, v_sz_boxed_1965_, v_i_boxed_1966_, v_bs_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v_as_1951_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_1968_, size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_bs_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1969_, v_i_1970_, v_bs_1971_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_1983_, lean_object* v_sz_1984_, lean_object* v_i_1985_, lean_object* v_bs_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
size_t v_sz_boxed_1997_; size_t v_i_boxed_1998_; lean_object* v_res_1999_; 
v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1984_);
lean_dec(v_sz_1984_);
v_i_boxed_1998_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_1983_, v_sz_boxed_1997_, v_i_boxed_1998_, v_bs_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v_as_1983_);
return v_res_1999_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Driver(builtin);
}
#ifdef __cplusplus
}
#endif
