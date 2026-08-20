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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
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
lean_object* v_ks_122_; lean_object* v_vs_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_141_; 
v_ks_122_ = lean_ctor_get(v_x_71_, 0);
v_vs_123_ = lean_ctor_get(v_x_71_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_141_ == 0)
{
v___x_125_ = v_x_71_;
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_vs_123_);
lean_inc(v_ks_122_);
lean_dec(v_x_71_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_141_;
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
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_ks_122_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_vs_123_);
v___x_128_ = v_reuseFailAlloc_140_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v_newNode_129_; size_t v___x_130_; uint8_t v___x_131_; 
v_newNode_129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_128_, v_x_74_, v_x_75_);
v___x_130_ = ((size_t)7ULL);
v___x_131_ = lean_usize_dec_le(v___x_130_, v_x_73_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_129_);
v___x_133_ = lean_unsigned_to_nat(4u);
v___x_134_ = lean_nat_dec_lt(v___x_132_, v___x_133_);
lean_dec(v___x_132_);
if (v___x_134_ == 0)
{
lean_object* v_ks_135_; lean_object* v_vs_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_ks_135_ = lean_ctor_get(v_newNode_129_, 0);
lean_inc_ref(v_ks_135_);
v_vs_136_ = lean_ctor_get(v_newNode_129_, 1);
lean_inc_ref(v_vs_136_);
lean_dec_ref(v_newNode_129_);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_139_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_73_, v_ks_135_, v_vs_136_, v___x_137_, v___x_138_);
lean_dec_ref(v_vs_136_);
lean_dec_ref(v_ks_135_);
return v___x_139_;
}
else
{
return v_newNode_129_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t v_depth_142_, lean_object* v_keys_143_, lean_object* v_vals_144_, lean_object* v_i_145_, lean_object* v_entries_146_){
_start:
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_array_get_size(v_keys_143_);
v___x_148_ = lean_nat_dec_lt(v_i_145_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec(v_i_145_);
return v_entries_146_;
}
else
{
lean_object* v_k_149_; lean_object* v_v_150_; uint64_t v___x_151_; size_t v_h_152_; size_t v___x_153_; lean_object* v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v_h_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_k_149_ = lean_array_fget_borrowed(v_keys_143_, v_i_145_);
v_v_150_ = lean_array_fget_borrowed(v_vals_144_, v_i_145_);
v___x_151_ = l_Lean_instHashableMVarId_hash(v_k_149_);
v_h_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = ((size_t)5ULL);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_sub(v_depth_142_, v___x_155_);
v___x_157_ = lean_usize_mul(v___x_153_, v___x_156_);
v_h_158_ = lean_usize_shift_right(v_h_152_, v___x_157_);
v___x_159_ = lean_nat_add(v_i_145_, v___x_154_);
lean_dec(v_i_145_);
lean_inc(v_v_150_);
lean_inc(v_k_149_);
v___x_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_146_, v_h_158_, v_depth_142_, v_k_149_, v_v_150_);
v_i_145_ = v___x_159_;
v_entries_146_ = v___x_160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_depth_162_, lean_object* v_keys_163_, lean_object* v_vals_164_, lean_object* v_i_165_, lean_object* v_entries_166_){
_start:
{
size_t v_depth_boxed_167_; lean_object* v_res_168_; 
v_depth_boxed_167_ = lean_unbox_usize(v_depth_162_);
lean_dec(v_depth_162_);
v_res_168_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_167_, v_keys_163_, v_vals_164_, v_i_165_, v_entries_166_);
lean_dec_ref(v_vals_164_);
lean_dec_ref(v_keys_163_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
size_t v_x_14452__boxed_174_; size_t v_x_14453__boxed_175_; lean_object* v_res_176_; 
v_x_14452__boxed_174_ = lean_unbox_usize(v_x_170_);
lean_dec(v_x_170_);
v_x_14453__boxed_175_ = lean_unbox_usize(v_x_171_);
lean_dec(v_x_171_);
v_res_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_169_, v_x_14452__boxed_174_, v_x_14453__boxed_175_, v_x_172_, v_x_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
uint64_t v___x_180_; size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_180_ = l_Lean_instHashableMVarId_hash(v_x_178_);
v___x_181_ = lean_uint64_to_usize(v___x_180_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_177_, v___x_181_, v___x_182_, v_x_178_, v_x_179_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_184_, lean_object* v_val_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; lean_object* v_mctx_189_; lean_object* v_cache_190_; lean_object* v_zetaDeltaFVarIds_191_; lean_object* v_postponed_192_; lean_object* v_diag_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_222_; 
v___x_188_ = lean_st_ref_take(v___y_186_);
v_mctx_189_ = lean_ctor_get(v___x_188_, 0);
v_cache_190_ = lean_ctor_get(v___x_188_, 1);
v_zetaDeltaFVarIds_191_ = lean_ctor_get(v___x_188_, 2);
v_postponed_192_ = lean_ctor_get(v___x_188_, 3);
v_diag_193_ = lean_ctor_get(v___x_188_, 4);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_222_ == 0)
{
v___x_195_ = v___x_188_;
v_isShared_196_ = v_isSharedCheck_222_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_diag_193_);
lean_inc(v_postponed_192_);
lean_inc(v_zetaDeltaFVarIds_191_);
lean_inc(v_cache_190_);
lean_inc(v_mctx_189_);
lean_dec(v___x_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_222_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_depth_197_; lean_object* v_levelAssignDepth_198_; lean_object* v_lmvarCounter_199_; lean_object* v_mvarCounter_200_; lean_object* v_lDecls_201_; lean_object* v_decls_202_; lean_object* v_userNames_203_; lean_object* v_lAssignment_204_; lean_object* v_eAssignment_205_; lean_object* v_dAssignment_206_; lean_object* v_instanceTypedMVars_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_221_; 
v_depth_197_ = lean_ctor_get(v_mctx_189_, 0);
v_levelAssignDepth_198_ = lean_ctor_get(v_mctx_189_, 1);
v_lmvarCounter_199_ = lean_ctor_get(v_mctx_189_, 2);
v_mvarCounter_200_ = lean_ctor_get(v_mctx_189_, 3);
v_lDecls_201_ = lean_ctor_get(v_mctx_189_, 4);
v_decls_202_ = lean_ctor_get(v_mctx_189_, 5);
v_userNames_203_ = lean_ctor_get(v_mctx_189_, 6);
v_lAssignment_204_ = lean_ctor_get(v_mctx_189_, 7);
v_eAssignment_205_ = lean_ctor_get(v_mctx_189_, 8);
v_dAssignment_206_ = lean_ctor_get(v_mctx_189_, 9);
v_instanceTypedMVars_207_ = lean_ctor_get(v_mctx_189_, 10);
v_isSharedCheck_221_ = !lean_is_exclusive(v_mctx_189_);
if (v_isSharedCheck_221_ == 0)
{
v___x_209_ = v_mctx_189_;
v_isShared_210_ = v_isSharedCheck_221_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_instanceTypedMVars_207_);
lean_inc(v_dAssignment_206_);
lean_inc(v_eAssignment_205_);
lean_inc(v_lAssignment_204_);
lean_inc(v_userNames_203_);
lean_inc(v_decls_202_);
lean_inc(v_lDecls_201_);
lean_inc(v_mvarCounter_200_);
lean_inc(v_lmvarCounter_199_);
lean_inc(v_levelAssignDepth_198_);
lean_inc(v_depth_197_);
lean_dec(v_mctx_189_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_221_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_205_, v_mvarId_184_, v_val_185_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 8, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_depth_197_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_levelAssignDepth_198_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_lmvarCounter_199_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_mvarCounter_200_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_lDecls_201_);
lean_ctor_set(v_reuseFailAlloc_220_, 5, v_decls_202_);
lean_ctor_set(v_reuseFailAlloc_220_, 6, v_userNames_203_);
lean_ctor_set(v_reuseFailAlloc_220_, 7, v_lAssignment_204_);
lean_ctor_set(v_reuseFailAlloc_220_, 8, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_220_, 9, v_dAssignment_206_);
lean_ctor_set(v_reuseFailAlloc_220_, 10, v_instanceTypedMVars_207_);
v___x_213_ = v_reuseFailAlloc_220_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_213_);
v___x_215_ = v___x_195_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_cache_190_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_zetaDeltaFVarIds_191_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_postponed_192_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_diag_193_);
v___x_215_ = v_reuseFailAlloc_219_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_st_ref_put(v___y_186_, v___x_215_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_223_, lean_object* v_val_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_223_, v_val_224_, v___y_225_);
lean_dec(v___y_225_);
return v_res_227_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_keys_228_, lean_object* v_i_229_, lean_object* v_k_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_keys_228_);
v___x_232_ = lean_nat_dec_lt(v_i_229_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v_i_229_);
return v___x_232_;
}
else
{
lean_object* v_k_x27_233_; uint8_t v___x_234_; 
v_k_x27_233_ = lean_array_fget_borrowed(v_keys_228_, v_i_229_);
v___x_234_ = l_Lean_instBEqMVarId_beq(v_k_230_, v_k_x27_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_add(v_i_229_, v___x_235_);
lean_dec(v_i_229_);
v_i_229_ = v___x_236_;
goto _start;
}
else
{
lean_dec(v_i_229_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_keys_238_, lean_object* v_i_239_, lean_object* v_k_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_238_, v_i_239_, v_k_240_);
lean_dec(v_k_240_);
lean_dec_ref(v_keys_238_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_243_, size_t v_x_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v_es_246_; lean_object* v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v_j_250_; lean_object* v___x_251_; 
v_es_246_ = lean_ctor_get(v_x_243_, 0);
v___x_247_ = lean_box(2);
v___x_248_ = ((size_t)31ULL);
v___x_249_ = lean_usize_land(v_x_244_, v___x_248_);
v_j_250_ = lean_usize_to_nat(v___x_249_);
v___x_251_ = lean_array_get_borrowed(v___x_247_, v_es_246_, v_j_250_);
lean_dec(v_j_250_);
switch(lean_obj_tag(v___x_251_))
{
case 0:
{
lean_object* v_key_252_; uint8_t v___x_253_; 
v_key_252_ = lean_ctor_get(v___x_251_, 0);
v___x_253_ = l_Lean_instBEqMVarId_beq(v_x_245_, v_key_252_);
return v___x_253_;
}
case 1:
{
lean_object* v_node_254_; size_t v___x_255_; size_t v___x_256_; 
v_node_254_ = lean_ctor_get(v___x_251_, 0);
v___x_255_ = ((size_t)5ULL);
v___x_256_ = lean_usize_shift_right(v_x_244_, v___x_255_);
v_x_243_ = v_node_254_;
v_x_244_ = v___x_256_;
goto _start;
}
default: 
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
else
{
lean_object* v_ks_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_ks_259_ = lean_ctor_get(v_x_243_, 0);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_259_, v___x_260_, v_x_245_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
size_t v_x_14674__boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_x_14674__boxed_265_ = lean_unbox_usize(v_x_263_);
lean_dec(v_x_263_);
v_res_266_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_262_, v_x_14674__boxed_265_, v_x_264_);
lean_dec(v_x_264_);
lean_dec_ref(v_x_262_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint64_t v___x_270_; size_t v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_instHashableMVarId_hash(v_x_269_);
v___x_271_ = lean_uint64_to_usize(v___x_270_);
v___x_272_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_268_, v___x_271_, v_x_269_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_273_, v_x_274_);
lean_dec(v_x_274_);
lean_dec_ref(v_x_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; lean_object* v_mctx_281_; lean_object* v_eAssignment_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = lean_st_ref_get(v___y_278_);
v_mctx_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_mctx_281_);
lean_dec(v___x_280_);
v_eAssignment_282_ = lean_ctor_get(v_mctx_281_, 8);
lean_inc_ref(v_eAssignment_282_);
lean_dec_ref(v_mctx_281_);
v___x_283_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_282_, v_mvarId_277_);
lean_dec_ref(v_eAssignment_282_);
v___x_284_ = lean_box(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec(v_mvarId_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object* v___f_301_, lean_object* v_mv_302_, lean_object* v_val_303_, lean_object* v_tac_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_fileName_358_; lean_object* v_fileMap_359_; lean_object* v_options_360_; lean_object* v_currRecDepth_361_; lean_object* v_maxRecDepth_362_; lean_object* v_ref_363_; lean_object* v_currNamespace_364_; lean_object* v_openDecls_365_; lean_object* v_initHeartbeats_366_; lean_object* v_maxHeartbeats_367_; lean_object* v_quotContext_368_; lean_object* v_currMacroScope_369_; uint8_t v_diag_370_; lean_object* v_cancelTk_x3f_371_; uint8_t v_suppressElabErrors_372_; lean_object* v_inheritedTraceOptions_373_; lean_object* v_keyedConfig_374_; uint8_t v_trackZetaDelta_375_; lean_object* v_zetaDeltaSet_376_; lean_object* v_lctx_377_; lean_object* v_localInstances_378_; lean_object* v_defEqCtx_x3f_379_; lean_object* v_synthPendingDepth_380_; lean_object* v_customCanUnfoldPredicate_x3f_381_; uint8_t v_univApprox_382_; uint8_t v_inTypeClassResolution_383_; uint8_t v_cacheInferType_384_; lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v_ref_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_box(0);
v___x_314_ = 1;
v___x_318_ = lean_box(1);
v___x_319_ = 0;
v___x_356_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2));
v___x_357_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_357_, 0, v___x_312_);
lean_ctor_set(v___x_357_, 1, v___x_313_);
lean_ctor_set(v___x_357_, 2, v___x_312_);
lean_ctor_set(v___x_357_, 3, v___f_301_);
lean_ctor_set(v___x_357_, 4, v___x_318_);
lean_ctor_set(v___x_357_, 5, v___x_318_);
lean_ctor_set(v___x_357_, 6, v___x_312_);
lean_ctor_set(v___x_357_, 7, v___x_356_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8, v___x_314_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 1, v___x_314_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 2, v___x_314_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 3, v___x_314_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 4, v___x_319_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 5, v___x_319_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 6, v___x_319_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 7, v___x_319_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 8, v___x_314_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 9, v___x_319_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*8 + 10, v___x_314_);
v_fileName_358_ = lean_ctor_get(v___y_309_, 0);
v_fileMap_359_ = lean_ctor_get(v___y_309_, 1);
v_options_360_ = lean_ctor_get(v___y_309_, 2);
v_currRecDepth_361_ = lean_ctor_get(v___y_309_, 3);
v_maxRecDepth_362_ = lean_ctor_get(v___y_309_, 4);
v_ref_363_ = lean_ctor_get(v___y_309_, 5);
v_currNamespace_364_ = lean_ctor_get(v___y_309_, 6);
v_openDecls_365_ = lean_ctor_get(v___y_309_, 7);
v_initHeartbeats_366_ = lean_ctor_get(v___y_309_, 8);
v_maxHeartbeats_367_ = lean_ctor_get(v___y_309_, 9);
v_quotContext_368_ = lean_ctor_get(v___y_309_, 10);
v_currMacroScope_369_ = lean_ctor_get(v___y_309_, 11);
v_diag_370_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*14);
v_cancelTk_x3f_371_ = lean_ctor_get(v___y_309_, 12);
v_suppressElabErrors_372_ = lean_ctor_get_uint8(v___y_309_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_373_ = lean_ctor_get(v___y_309_, 13);
v_keyedConfig_374_ = lean_ctor_get(v___y_307_, 0);
v_trackZetaDelta_375_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*7);
v_zetaDeltaSet_376_ = lean_ctor_get(v___y_307_, 1);
v_lctx_377_ = lean_ctor_get(v___y_307_, 2);
v_localInstances_378_ = lean_ctor_get(v___y_307_, 3);
v_defEqCtx_x3f_379_ = lean_ctor_get(v___y_307_, 4);
v_synthPendingDepth_380_ = lean_ctor_get(v___y_307_, 5);
v_customCanUnfoldPredicate_x3f_381_ = lean_ctor_get(v___y_307_, 6);
v_univApprox_382_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_383_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*7 + 2);
v_cacheInferType_384_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*7 + 3);
v___x_385_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3));
v___x_386_ = 1;
v_ref_387_ = l_Lean_replaceRef(v_val_303_, v_ref_363_);
lean_inc_ref(v_inheritedTraceOptions_373_);
lean_inc(v_cancelTk_x3f_371_);
lean_inc(v_currMacroScope_369_);
lean_inc(v_quotContext_368_);
lean_inc(v_maxHeartbeats_367_);
lean_inc(v_initHeartbeats_366_);
lean_inc(v_openDecls_365_);
lean_inc(v_currNamespace_364_);
lean_inc(v_maxRecDepth_362_);
lean_inc(v_currRecDepth_361_);
lean_inc_ref(v_options_360_);
lean_inc_ref(v_fileMap_359_);
lean_inc_ref(v_fileName_358_);
v___x_388_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_388_, 0, v_fileName_358_);
lean_ctor_set(v___x_388_, 1, v_fileMap_359_);
lean_ctor_set(v___x_388_, 2, v_options_360_);
lean_ctor_set(v___x_388_, 3, v_currRecDepth_361_);
lean_ctor_set(v___x_388_, 4, v_maxRecDepth_362_);
lean_ctor_set(v___x_388_, 5, v_ref_387_);
lean_ctor_set(v___x_388_, 6, v_currNamespace_364_);
lean_ctor_set(v___x_388_, 7, v_openDecls_365_);
lean_ctor_set(v___x_388_, 8, v_initHeartbeats_366_);
lean_ctor_set(v___x_388_, 9, v_maxHeartbeats_367_);
lean_ctor_set(v___x_388_, 10, v_quotContext_368_);
lean_ctor_set(v___x_388_, 11, v_currMacroScope_369_);
lean_ctor_set(v___x_388_, 12, v_cancelTk_x3f_371_);
lean_ctor_set(v___x_388_, 13, v_inheritedTraceOptions_373_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*14, v_diag_370_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*14 + 1, v_suppressElabErrors_372_);
lean_inc_ref(v_keyedConfig_374_);
v___x_389_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_386_, v_keyedConfig_374_);
lean_inc(v_customCanUnfoldPredicate_x3f_381_);
lean_inc(v_synthPendingDepth_380_);
lean_inc(v_defEqCtx_x3f_379_);
lean_inc_ref(v_localInstances_378_);
lean_inc_ref(v_lctx_377_);
lean_inc(v_zetaDeltaSet_376_);
v___x_390_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_zetaDeltaSet_376_);
lean_ctor_set(v___x_390_, 2, v_lctx_377_);
lean_ctor_set(v___x_390_, 3, v_localInstances_378_);
lean_ctor_set(v___x_390_, 4, v_defEqCtx_x3f_379_);
lean_ctor_set(v___x_390_, 5, v_synthPendingDepth_380_);
lean_ctor_set(v___x_390_, 6, v_customCanUnfoldPredicate_x3f_381_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*7, v_trackZetaDelta_375_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*7 + 1, v_univApprox_382_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*7 + 2, v_inTypeClassResolution_383_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*7 + 3, v_cacheInferType_384_);
lean_inc(v_mv_302_);
v___x_391_ = l_Lean_Elab_runTactic(v_mv_302_, v_tac_304_, v___x_357_, v___x_385_, v___x_390_, v___y_308_, v___x_388_, v___y_310_);
lean_dec_ref_known(v___x_388_, 14);
lean_dec_ref_known(v___x_390_, 7);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_dec_ref_known(v___x_391_, 1);
goto v___jp_320_;
}
else
{
if (lean_obj_tag(v___x_391_) == 0)
{
lean_dec_ref_known(v___x_391_, 1);
goto v___jp_320_;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec(v_mv_302_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
v___jp_315_:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0));
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
v___jp_320_:
{
lean_object* v___x_321_; lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_355_; 
v___x_321_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mv_302_, v___y_308_);
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_355_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_355_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_355_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint8_t v___x_326_; 
v___x_326_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec(v_mv_302_);
v___x_327_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_327_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
else
{
lean_object* v___x_331_; lean_object* v_a_332_; 
lean_del_object(v___x_324_);
v___x_331_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mv_302_, v___y_308_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref(v___x_331_);
if (lean_obj_tag(v_a_332_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; 
v_val_333_ = lean_ctor_get(v_a_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v_a_332_, 1);
v___x_334_ = l_Lean_Meta_Sym_unfoldReducible(v_val_333_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = l_Lean_Meta_Sym_shareCommon(v_a_335_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mv_302_, v_a_337_, v___y_308_);
lean_dec_ref(v___x_338_);
goto v___jp_315_;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_mv_302_);
v_a_339_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_336_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_336_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_mv_302_);
v_a_347_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_334_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_334_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_dec(v_a_332_);
lean_dec(v_mv_302_);
goto v___jp_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_400_, lean_object* v_mv_401_, lean_object* v_val_402_, lean_object* v_tac_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_400_, v_mv_401_, v_val_402_, v_tac_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v_val_402_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
else
{
lean_object* v_key_415_; lean_object* v_value_416_; lean_object* v_tail_417_; uint8_t v___x_418_; 
v_key_415_ = lean_ctor_get(v_x_413_, 0);
v_value_416_ = lean_ctor_get(v_x_413_, 1);
v_tail_417_ = lean_ctor_get(v_x_413_, 2);
v___x_418_ = lean_nat_dec_eq(v_key_415_, v_a_412_);
if (v___x_418_ == 0)
{
v_x_413_ = v_tail_417_;
goto _start;
}
else
{
lean_object* v___x_420_; 
lean_inc(v_value_416_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_value_416_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_421_, v_x_422_);
lean_dec(v_x_422_);
lean_dec(v_a_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_buckets_426_; lean_object* v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v_fold_431_; uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_buckets_426_ = lean_ctor_get(v_m_424_, 1);
v___x_427_ = lean_array_get_size(v_buckets_426_);
v___x_428_ = lean_uint64_of_nat(v_a_425_);
v___x_429_ = 32ULL;
v___x_430_ = lean_uint64_shift_right(v___x_428_, v___x_429_);
v_fold_431_ = lean_uint64_xor(v___x_428_, v___x_430_);
v___x_432_ = 16ULL;
v___x_433_ = lean_uint64_shift_right(v_fold_431_, v___x_432_);
v___x_434_ = lean_uint64_xor(v_fold_431_, v___x_433_);
v___x_435_ = lean_uint64_to_usize(v___x_434_);
v___x_436_ = lean_usize_of_nat(v___x_427_);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_sub(v___x_436_, v___x_437_);
v___x_439_ = lean_usize_land(v___x_435_, v___x_438_);
v___x_440_ = lean_array_uget_borrowed(v_buckets_426_, v___x_439_);
v___x_441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_425_, v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_m_442_);
return v_res_444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Array_mkArray0(lean_box(0));
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object* v_invariantAlts_509_, lean_object* v_n_510_, lean_object* v_mv_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_526_; lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_509_, v_n_510_);
if (lean_obj_tag(v___x_539_) == 1)
{
lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_611_; 
v_val_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_611_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_611_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_611_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___f_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___f_544_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0));
v___x_545_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5));
lean_inc(v_val_540_);
v___x_546_ = l_Lean_Syntax_isOfKind(v_val_540_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7));
lean_inc(v_val_540_);
v___x_548_ = l_Lean_Syntax_isOfKind(v_val_540_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_val_540_);
lean_dec(v_mv_511_);
v___x_549_ = lean_box(v___x_548_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
lean_ctor_set(v___x_542_, 0, v___x_549_);
v___x_551_ = v___x_542_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = l_Lean_Syntax_getArg(v_val_540_, v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9));
lean_inc(v___x_554_);
v___x_556_ = l_Lean_Syntax_isOfKind(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v___x_554_);
lean_dec(v_val_540_);
lean_dec(v_mv_511_);
v___x_557_ = lean_box(v___x_556_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
lean_ctor_set(v___x_542_, 0, v___x_557_);
v___x_559_ = v___x_542_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v_ref_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_args_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
lean_del_object(v___x_542_);
v_ref_561_ = lean_ctor_get(v_a_516_, 5);
v___x_562_ = l_Lean_Syntax_getArg(v___x_554_, v___x_553_);
lean_dec(v___x_554_);
v___x_563_ = lean_unsigned_to_nat(3u);
v___x_564_ = l_Lean_Syntax_getArg(v_val_540_, v___x_563_);
v_args_565_ = l_Lean_Syntax_getArgs(v___x_562_);
lean_dec(v___x_562_);
v___x_566_ = l_Lean_SourceInfo_fromRef(v_ref_561_, v___x_546_);
v___x_567_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11));
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_566_, 11);
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14));
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16));
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18));
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20));
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21));
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_566_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22);
v___x_577_ = l_Array_append___redArg(v___x_576_, v_args_565_);
lean_dec_ref(v_args_565_);
v___x_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_578_, 0, v___x_566_);
lean_ctor_set(v___x_578_, 1, v___x_572_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
v___x_579_ = l_Lean_Syntax_node2(v___x_566_, v___x_573_, v___x_575_, v___x_578_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23));
v___x_581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_566_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_583_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
v___x_584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_566_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
v___x_585_ = l_Lean_Syntax_node2(v___x_566_, v___x_583_, v___x_584_, v___x_564_);
v___x_586_ = l_Lean_Syntax_node3(v___x_566_, v___x_572_, v___x_579_, v___x_581_, v___x_585_);
v___x_587_ = l_Lean_Syntax_node1(v___x_566_, v___x_571_, v___x_586_);
v___x_588_ = l_Lean_Syntax_node1(v___x_566_, v___x_570_, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26));
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_566_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_Syntax_node3(v___x_566_, v___x_567_, v___x_569_, v___x_588_, v___x_590_);
v___x_592_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_544_, v_mv_511_, v_val_540_, v___x_591_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_val_540_);
v___y_526_ = v___x_592_;
goto v___jp_525_;
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l_Lean_Syntax_getArg(v_val_540_, v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28));
v___x_596_ = l_Lean_Syntax_isOfKind(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec(v_val_540_);
lean_dec(v_mv_511_);
v___x_597_ = lean_box(v___x_596_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
lean_ctor_set(v___x_542_, 0, v___x_597_);
v___x_599_ = v___x_542_;
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
lean_object* v_ref_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_del_object(v___x_542_);
v_ref_601_ = lean_ctor_get(v_a_516_, 5);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = l_Lean_Syntax_getArg(v_val_540_, v___x_602_);
v___x_604_ = 0;
v___x_605_ = l_Lean_SourceInfo_fromRef(v_ref_601_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_607_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
lean_inc(v___x_605_);
v___x_608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
v___x_609_ = l_Lean_Syntax_node2(v___x_605_, v___x_607_, v___x_608_, v___x_603_);
v___x_610_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_544_, v_mv_511_, v_val_540_, v___x_609_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_val_540_);
v___y_526_ = v___x_610_;
goto v___jp_525_;
}
}
}
}
else
{
uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v___x_539_);
lean_dec(v_mv_511_);
v___x_612_ = 0;
v___x_613_ = lean_box(v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
v___jp_519_:
{
if (v___y_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v___y_520_);
v___x_522_ = lean_box(v___y_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___y_520_);
return v___x_524_;
}
}
v___jp_525_:
{
if (lean_obj_tag(v___y_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_535_; 
v_a_527_ = lean_ctor_get(v___y_526_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___y_526_);
if (v_isSharedCheck_535_ == 0)
{
v___x_529_ = v___y_526_;
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___y_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_a_531_; lean_object* v___x_533_; 
v_a_531_ = lean_ctor_get(v_a_527_, 0);
lean_inc(v_a_531_);
lean_dec(v_a_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_a_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
else
{
lean_object* v_a_536_; uint8_t v___x_537_; 
v_a_536_ = lean_ctor_get(v___y_526_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___y_526_, 1);
v___x_537_ = l_Lean_Exception_isInterrupt(v_a_536_);
if (v___x_537_ == 0)
{
uint8_t v___x_538_; 
lean_inc(v_a_536_);
v___x_538_ = l_Lean_Exception_isRuntime(v_a_536_);
v___y_520_ = v_a_536_;
v___y_521_ = v___x_538_;
goto v___jp_519_;
}
else
{
v___y_520_ = v_a_536_;
v___y_521_ = v___x_537_;
goto v___jp_519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_615_, lean_object* v_n_616_, lean_object* v_mv_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_615_, v_n_616_, v_mv_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_n_616_);
lean_dec_ref(v_invariantAlts_615_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_626_, lean_object* v_m_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_627_, v_a_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_630_, lean_object* v_m_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(v_00_u03b2_630_, v_m_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_m_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_634_, v___y_638_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_mvarId_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v_mvarId_643_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_652_, lean_object* v_val_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_652_, v_val_653_, v___y_657_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_662_, lean_object* v_val_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_662_, v_val_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_672_, lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_676_, lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_676_, v_a_677_, v_x_678_);
lean_dec(v_x_678_);
lean_dec(v_a_677_);
return v_res_679_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_681_, v_x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_684_, v_x_685_, v_x_686_);
lean_dec(v_x_686_);
lean_dec_ref(v_x_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_690_, v_x_691_, v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, size_t v_x_696_, lean_object* v_x_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
size_t v_x_15441__boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_x_15441__boxed_703_ = lean_unbox_usize(v_x_701_);
lean_dec(v_x_701_);
v_res_704_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_699_, v_x_700_, v_x_15441__boxed_703_, v_x_702_);
lean_dec(v_x_702_);
lean_dec_ref(v_x_700_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_706_, lean_object* v_x_707_, size_t v_x_708_, size_t v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_707_, v_x_708_, v_x_709_, v_x_710_, v_x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
size_t v_x_15452__boxed_719_; size_t v_x_15453__boxed_720_; lean_object* v_res_721_; 
v_x_15452__boxed_719_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_x_15453__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_713_, v_x_714_, v_x_15452__boxed_719_, v_x_15453__boxed_720_, v_x_717_, v_x_718_);
return v_res_721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_722_, lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_heq_725_, lean_object* v_i_726_, lean_object* v_k_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_723_, v_i_726_, v_k_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_heq_732_, lean_object* v_i_733_, lean_object* v_k_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_729_, v_keys_730_, v_vals_731_, v_heq_732_, v_i_733_, v_k_734_);
lean_dec(v_k_734_);
lean_dec_ref(v_vals_731_);
lean_dec_ref(v_keys_730_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_737_, lean_object* v_n_738_, lean_object* v_k_739_, lean_object* v_v_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_738_, v_k_739_, v_v_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_742_, size_t v_depth_743_, lean_object* v_keys_744_, lean_object* v_vals_745_, lean_object* v_heq_746_, lean_object* v_i_747_, lean_object* v_entries_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_743_, v_keys_744_, v_vals_745_, v_i_747_, v_entries_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_750_, lean_object* v_depth_751_, lean_object* v_keys_752_, lean_object* v_vals_753_, lean_object* v_heq_754_, lean_object* v_i_755_, lean_object* v_entries_756_){
_start:
{
size_t v_depth_boxed_757_; lean_object* v_res_758_; 
v_depth_boxed_757_ = lean_unbox_usize(v_depth_751_);
lean_dec(v_depth_751_);
v_res_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_750_, v_depth_boxed_757_, v_keys_752_, v_vals_753_, v_heq_754_, v_i_755_, v_entries_756_);
lean_dec_ref(v_vals_753_);
lean_dec_ref(v_keys_752_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_760_, v_x_761_, v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
return v_x_765_;
}
else
{
lean_object* v_key_767_; lean_object* v_value_768_; lean_object* v_tail_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_792_; 
v_key_767_ = lean_ctor_get(v_x_766_, 0);
v_value_768_ = lean_ctor_get(v_x_766_, 1);
v_tail_769_ = lean_ctor_get(v_x_766_, 2);
v_isSharedCheck_792_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_792_ == 0)
{
v___x_771_ = v_x_766_;
v_isShared_772_ = v_isSharedCheck_792_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_tail_769_);
lean_inc(v_value_768_);
lean_inc(v_key_767_);
lean_dec(v_x_766_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_792_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint64_t v___x_774_; uint64_t v___x_775_; uint64_t v___x_776_; uint64_t v_fold_777_; uint64_t v___x_778_; uint64_t v___x_779_; uint64_t v___x_780_; size_t v___x_781_; size_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_773_ = lean_array_get_size(v_x_765_);
v___x_774_ = lean_uint64_of_nat(v_key_767_);
v___x_775_ = 32ULL;
v___x_776_ = lean_uint64_shift_right(v___x_774_, v___x_775_);
v_fold_777_ = lean_uint64_xor(v___x_774_, v___x_776_);
v___x_778_ = 16ULL;
v___x_779_ = lean_uint64_shift_right(v_fold_777_, v___x_778_);
v___x_780_ = lean_uint64_xor(v_fold_777_, v___x_779_);
v___x_781_ = lean_uint64_to_usize(v___x_780_);
v___x_782_ = lean_usize_of_nat(v___x_773_);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_sub(v___x_782_, v___x_783_);
v___x_785_ = lean_usize_land(v___x_781_, v___x_784_);
v___x_786_ = lean_array_uget_borrowed(v_x_765_, v___x_785_);
lean_inc(v___x_786_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 2, v___x_786_);
v___x_788_ = v___x_771_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_key_767_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_value_768_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___x_786_);
v___x_788_ = v_reuseFailAlloc_791_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; 
v___x_789_ = lean_array_uset(v_x_765_, v___x_785_, v___x_788_);
v_x_765_ = v___x_789_;
v_x_766_ = v_tail_769_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_793_, lean_object* v_source_794_, lean_object* v_target_795_){
_start:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_array_get_size(v_source_794_);
v___x_797_ = lean_nat_dec_lt(v_i_793_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_source_794_);
lean_dec(v_i_793_);
return v_target_795_;
}
else
{
lean_object* v_es_798_; lean_object* v___x_799_; lean_object* v_source_800_; lean_object* v_target_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_es_798_ = lean_array_fget(v_source_794_, v_i_793_);
v___x_799_ = lean_box(0);
v_source_800_ = lean_array_fset(v_source_794_, v_i_793_, v___x_799_);
v_target_801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_795_, v_es_798_);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_nat_add(v_i_793_, v___x_802_);
lean_dec(v_i_793_);
v_i_793_ = v___x_803_;
v_source_794_ = v_source_800_;
v_target_795_ = v_target_801_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_nbuckets_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_806_ = lean_array_get_size(v_data_805_);
v___x_807_ = lean_unsigned_to_nat(2u);
v_nbuckets_808_ = lean_nat_mul(v___x_806_, v___x_807_);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_box(0);
v___x_811_ = lean_mk_array(v_nbuckets_808_, v___x_810_);
v___x_812_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_809_, v_data_805_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
else
{
lean_object* v_key_816_; lean_object* v_tail_817_; uint8_t v___x_818_; 
v_key_816_ = lean_ctor_get(v_x_814_, 0);
v_tail_817_ = lean_ctor_get(v_x_814_, 2);
v___x_818_ = lean_nat_dec_eq(v_key_816_, v_a_813_);
if (v___x_818_ == 0)
{
v_x_814_ = v_tail_817_;
goto _start;
}
else
{
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec(v_a_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_824_, lean_object* v_a_825_, lean_object* v_b_826_){
_start:
{
lean_object* v_size_827_; lean_object* v_buckets_828_; lean_object* v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v_fold_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v_bkt_842_; uint8_t v___x_843_; 
v_size_827_ = lean_ctor_get(v_m_824_, 0);
v_buckets_828_ = lean_ctor_get(v_m_824_, 1);
v___x_829_ = lean_array_get_size(v_buckets_828_);
v___x_830_ = lean_uint64_of_nat(v_a_825_);
v___x_831_ = 32ULL;
v___x_832_ = lean_uint64_shift_right(v___x_830_, v___x_831_);
v_fold_833_ = lean_uint64_xor(v___x_830_, v___x_832_);
v___x_834_ = 16ULL;
v___x_835_ = lean_uint64_shift_right(v_fold_833_, v___x_834_);
v___x_836_ = lean_uint64_xor(v_fold_833_, v___x_835_);
v___x_837_ = lean_uint64_to_usize(v___x_836_);
v___x_838_ = lean_usize_of_nat(v___x_829_);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_sub(v___x_838_, v___x_839_);
v___x_841_ = lean_usize_land(v___x_837_, v___x_840_);
v_bkt_842_ = lean_array_uget_borrowed(v_buckets_828_, v___x_841_);
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_825_, v_bkt_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_864_; 
lean_inc_ref(v_buckets_828_);
lean_inc(v_size_827_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_m_824_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; 
v_unused_865_ = lean_ctor_get(v_m_824_, 1);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_m_824_, 0);
lean_dec(v_unused_866_);
v___x_845_ = v_m_824_;
v_isShared_846_ = v_isSharedCheck_864_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_m_824_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_864_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v_size_x27_848_; lean_object* v___x_849_; lean_object* v_buckets_x27_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_847_ = lean_unsigned_to_nat(1u);
v_size_x27_848_ = lean_nat_add(v_size_827_, v___x_847_);
lean_dec(v_size_827_);
lean_inc(v_bkt_842_);
v___x_849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_849_, 0, v_a_825_);
lean_ctor_set(v___x_849_, 1, v_b_826_);
lean_ctor_set(v___x_849_, 2, v_bkt_842_);
v_buckets_x27_850_ = lean_array_uset(v_buckets_828_, v___x_841_, v___x_849_);
v___x_851_ = lean_unsigned_to_nat(4u);
v___x_852_ = lean_nat_mul(v_size_x27_848_, v___x_851_);
v___x_853_ = lean_unsigned_to_nat(3u);
v___x_854_ = lean_nat_div(v___x_852_, v___x_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_array_get_size(v_buckets_x27_850_);
v___x_856_ = lean_nat_dec_le(v___x_854_, v___x_855_);
lean_dec(v___x_854_);
if (v___x_856_ == 0)
{
lean_object* v_val_857_; lean_object* v___x_859_; 
v_val_857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_850_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_val_857_);
lean_ctor_set(v___x_845_, 0, v_size_x27_848_);
v___x_859_ = v___x_845_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_size_x27_848_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_val_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_862_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_buckets_x27_850_);
lean_ctor_set(v___x_845_, 0, v_size_x27_848_);
v___x_862_ = v___x_845_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_size_x27_848_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_buckets_x27_850_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_dec(v_b_826_);
lean_dec(v_a_825_);
return v_m_824_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_867_, lean_object* v_as_x27_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
if (lean_obj_tag(v_as_x27_868_) == 0)
{
lean_object* v___x_879_; 
lean_dec_ref(v___x_867_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v_b_869_);
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v___x_882_; 
v_head_880_ = lean_ctor_get(v_as_x27_868_, 0);
v_tail_881_ = lean_ctor_get(v_as_x27_868_, 1);
lean_inc(v_head_880_);
v___x_882_ = l_Lean_MVarId_getType(v_head_880_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; uint8_t v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
lean_inc_ref(v___x_867_);
v___x_884_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_867_, v_a_883_);
lean_dec(v_a_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_inc(v_head_880_);
v___x_885_ = lean_array_push(v_b_869_, v_head_880_);
v_as_x27_868_ = v_tail_881_;
v_b_869_ = v___x_885_;
goto _start;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_specBackwardRuleCache_889_; lean_object* v_splitBackwardRuleCache_890_; lean_object* v_latticeBackwardRuleCache_891_; lean_object* v_frameBackwardRuleCache_892_; lean_object* v_frameDB_893_; lean_object* v_invariants_894_; lean_object* v_vcs_895_; lean_object* v_simpState_896_; lean_object* v_fuel_897_; lean_object* v_inlineHandledInvariants_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_956_; 
v___x_887_ = lean_st_ref_get(v___y_871_);
v___x_888_ = lean_st_ref_take(v___y_871_);
v_specBackwardRuleCache_889_ = lean_ctor_get(v___x_888_, 0);
v_splitBackwardRuleCache_890_ = lean_ctor_get(v___x_888_, 1);
v_latticeBackwardRuleCache_891_ = lean_ctor_get(v___x_888_, 2);
v_frameBackwardRuleCache_892_ = lean_ctor_get(v___x_888_, 3);
v_frameDB_893_ = lean_ctor_get(v___x_888_, 4);
v_invariants_894_ = lean_ctor_get(v___x_888_, 5);
v_vcs_895_ = lean_ctor_get(v___x_888_, 6);
v_simpState_896_ = lean_ctor_get(v___x_888_, 7);
v_fuel_897_ = lean_ctor_get(v___x_888_, 8);
v_inlineHandledInvariants_898_ = lean_ctor_get(v___x_888_, 9);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_956_ == 0)
{
v___x_900_ = v___x_888_;
v_isShared_901_ = v_isSharedCheck_956_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_inlineHandledInvariants_898_);
lean_inc(v_fuel_897_);
lean_inc(v_simpState_896_);
lean_inc(v_vcs_895_);
lean_inc(v_invariants_894_);
lean_inc(v_frameDB_893_);
lean_inc(v_frameBackwardRuleCache_892_);
lean_inc(v_latticeBackwardRuleCache_891_);
lean_inc(v_splitBackwardRuleCache_890_);
lean_inc(v_specBackwardRuleCache_889_);
lean_dec(v___x_888_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_956_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_inc(v_head_880_);
v___x_902_ = lean_array_push(v_invariants_894_, v_head_880_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 5, v___x_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_specBackwardRuleCache_889_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_splitBackwardRuleCache_890_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_latticeBackwardRuleCache_891_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_frameBackwardRuleCache_892_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_frameDB_893_);
lean_ctor_set(v_reuseFailAlloc_955_, 5, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_955_, 6, v_vcs_895_);
lean_ctor_set(v_reuseFailAlloc_955_, 7, v_simpState_896_);
lean_ctor_set(v_reuseFailAlloc_955_, 8, v_fuel_897_);
lean_ctor_set(v_reuseFailAlloc_955_, 9, v_inlineHandledInvariants_898_);
v___x_904_ = v_reuseFailAlloc_955_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v_invariants_906_; lean_object* v_invariantAlts_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_905_ = lean_st_ref_put(v___y_871_, v___x_904_);
v_invariants_906_ = lean_ctor_get(v___x_887_, 5);
lean_inc_ref(v_invariants_906_);
lean_dec(v___x_887_);
v_invariantAlts_907_ = lean_ctor_get(v___y_870_, 3);
v___x_908_ = lean_array_get_size(v_invariants_906_);
lean_dec_ref(v_invariants_906_);
v___x_909_ = lean_unsigned_to_nat(1u);
v___x_910_ = lean_nat_add(v___x_908_, v___x_909_);
lean_inc(v_head_880_);
v___x_911_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_907_, v___x_910_, v_head_880_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; uint8_t v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; lean_object* v___x_915_; 
lean_dec(v___x_910_);
v___x_914_ = 2;
lean_inc(v_head_880_);
v___x_915_ = l_Lean_MVarId_setKind___redArg(v_head_880_, v___x_914_, v___y_875_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_dec_ref_known(v___x_915_, 1);
v_as_x27_868_ = v_tail_881_;
goto _start;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_b_869_);
lean_dec_ref(v___x_867_);
v_a_917_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_915_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v___x_925_; lean_object* v_specBackwardRuleCache_926_; lean_object* v_splitBackwardRuleCache_927_; lean_object* v_latticeBackwardRuleCache_928_; lean_object* v_frameBackwardRuleCache_929_; lean_object* v_frameDB_930_; lean_object* v_invariants_931_; lean_object* v_vcs_932_; lean_object* v_simpState_933_; lean_object* v_fuel_934_; lean_object* v_inlineHandledInvariants_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_946_; 
v___x_925_ = lean_st_ref_take(v___y_871_);
v_specBackwardRuleCache_926_ = lean_ctor_get(v___x_925_, 0);
v_splitBackwardRuleCache_927_ = lean_ctor_get(v___x_925_, 1);
v_latticeBackwardRuleCache_928_ = lean_ctor_get(v___x_925_, 2);
v_frameBackwardRuleCache_929_ = lean_ctor_get(v___x_925_, 3);
v_frameDB_930_ = lean_ctor_get(v___x_925_, 4);
v_invariants_931_ = lean_ctor_get(v___x_925_, 5);
v_vcs_932_ = lean_ctor_get(v___x_925_, 6);
v_simpState_933_ = lean_ctor_get(v___x_925_, 7);
v_fuel_934_ = lean_ctor_get(v___x_925_, 8);
v_inlineHandledInvariants_935_ = lean_ctor_get(v___x_925_, 9);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_946_ == 0)
{
v___x_937_ = v___x_925_;
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_inlineHandledInvariants_935_);
lean_inc(v_fuel_934_);
lean_inc(v_simpState_933_);
lean_inc(v_vcs_932_);
lean_inc(v_invariants_931_);
lean_inc(v_frameDB_930_);
lean_inc(v_frameBackwardRuleCache_929_);
lean_inc(v_latticeBackwardRuleCache_928_);
lean_inc(v_splitBackwardRuleCache_927_);
lean_inc(v_specBackwardRuleCache_926_);
lean_dec(v___x_925_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_939_ = lean_box(0);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_935_, v___x_910_, v___x_939_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 9, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_specBackwardRuleCache_926_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_splitBackwardRuleCache_927_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_latticeBackwardRuleCache_928_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_frameBackwardRuleCache_929_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_frameDB_930_);
lean_ctor_set(v_reuseFailAlloc_945_, 5, v_invariants_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 6, v_vcs_932_);
lean_ctor_set(v_reuseFailAlloc_945_, 7, v_simpState_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 8, v_fuel_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 9, v___x_940_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; 
v___x_943_ = lean_st_ref_put(v___y_871_, v___x_942_);
v_as_x27_868_ = v_tail_881_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v___x_910_);
lean_dec_ref(v_b_869_);
lean_dec_ref(v___x_867_);
v_a_947_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_911_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_911_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v_b_869_);
lean_dec_ref(v___x_867_);
v_a_957_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_882_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_882_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_965_, lean_object* v_as_x27_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_965_, v_as_x27_966_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_as_x27_966_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; lean_object* v_env_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = lean_st_ref_get(v_a_991_);
v_env_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc_ref(v_env_994_);
lean_dec(v___x_993_);
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_996_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_994_, v_subgoals_980_, v___x_995_, v_a_981_, v_a_982_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_subgoals_997_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1011_, lean_object* v_m_1012_, lean_object* v_a_1013_, lean_object* v_b_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1012_, v_a_1013_, v_b_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1016_, lean_object* v_as_1017_, lean_object* v_as_x27_1018_, lean_object* v_b_1019_, lean_object* v_a_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1016_, v_as_x27_1018_, v_b_1019_, v___y_1021_, v___y_1022_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1034_ = _args[0];
lean_object* v_as_1035_ = _args[1];
lean_object* v_as_x27_1036_ = _args[2];
lean_object* v_b_1037_ = _args[3];
lean_object* v_a_1038_ = _args[4];
lean_object* v___y_1039_ = _args[5];
lean_object* v___y_1040_ = _args[6];
lean_object* v___y_1041_ = _args[7];
lean_object* v___y_1042_ = _args[8];
lean_object* v___y_1043_ = _args[9];
lean_object* v___y_1044_ = _args[10];
lean_object* v___y_1045_ = _args[11];
lean_object* v___y_1046_ = _args[12];
lean_object* v___y_1047_ = _args[13];
lean_object* v___y_1048_ = _args[14];
lean_object* v___y_1049_ = _args[15];
lean_object* v___y_1050_ = _args[16];
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(v___x_1034_, v_as_1035_, v_as_x27_1036_, v_b_1037_, v_a_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v_as_x27_1036_);
lean_dec(v_as_1035_);
return v_res_1051_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1052_, lean_object* v_a_1053_, lean_object* v_x_1054_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1053_, v_x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1056_, lean_object* v_a_1057_, lean_object* v_x_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1056_, v_a_1057_, v_x_1058_);
lean_dec(v_x_1058_);
lean_dec(v_a_1057_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1061_, lean_object* v_data_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1064_, lean_object* v_i_1065_, lean_object* v_source_1066_, lean_object* v_target_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1065_, v_source_1066_, v_target_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_toGoalState_1086_; lean_object* v_mvarId_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1183_; 
v_toGoalState_1086_ = lean_ctor_get(v_goal_1073_, 0);
v_mvarId_1087_ = lean_ctor_get(v_goal_1073_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_goal_1073_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1089_ = v_goal_1073_;
v_isShared_1090_ = v_isSharedCheck_1183_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_mvarId_1087_);
lean_inc(v_toGoalState_1086_);
lean_dec(v_goal_1073_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1183_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1087_, v_a_1074_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v_a_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_toGoalState_1086_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_a_1092_);
v___x_1094_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v___x_1094_, v_a_1074_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1165_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1165_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1165_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_toGoalState_1100_; uint8_t v_inconsistent_1101_; 
v_toGoalState_1100_ = lean_ctor_get(v_a_1096_, 0);
lean_inc_ref(v_toGoalState_1100_);
v_inconsistent_1101_ = lean_ctor_get_uint8(v_toGoalState_1100_, sizeof(void*)*17);
if (v_inconsistent_1101_ == 0)
{
lean_object* v_mvarId_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1098_);
v_mvarId_1102_ = lean_ctor_get(v_a_1096_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_a_1096_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_a_1096_, 0);
lean_dec(v_unused_1160_);
v___x_1104_ = v_a_1096_;
v_isShared_1105_ = v_isSharedCheck_1159_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_mvarId_1102_);
lean_dec(v_a_1096_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1159_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_mvarId_1102_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1150_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1150_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1150_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
if (lean_obj_tag(v_a_1107_) == 1)
{
lean_object* v_val_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
lean_del_object(v___x_1109_);
v_val_1111_ = lean_ctor_get(v_a_1107_, 0);
lean_inc_n(v_val_1111_, 2);
lean_dec_ref_known(v_a_1107_, 1);
v___x_1112_ = 2;
v___x_1113_ = l_Lean_MVarId_setKind___redArg(v_val_1111_, v___x_1112_, v_a_1082_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1144_; 
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1113_, 0);
lean_dec(v_unused_1145_);
v___x_1115_ = v___x_1113_;
v_isShared_1116_ = v_isSharedCheck_1144_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v___x_1113_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1144_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v_specBackwardRuleCache_1118_; lean_object* v_splitBackwardRuleCache_1119_; lean_object* v_latticeBackwardRuleCache_1120_; lean_object* v_frameBackwardRuleCache_1121_; lean_object* v_frameDB_1122_; lean_object* v_invariants_1123_; lean_object* v_vcs_1124_; lean_object* v_simpState_1125_; lean_object* v_fuel_1126_; lean_object* v_inlineHandledInvariants_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1143_; 
v___x_1117_ = lean_st_ref_take(v_a_1075_);
v_specBackwardRuleCache_1118_ = lean_ctor_get(v___x_1117_, 0);
v_splitBackwardRuleCache_1119_ = lean_ctor_get(v___x_1117_, 1);
v_latticeBackwardRuleCache_1120_ = lean_ctor_get(v___x_1117_, 2);
v_frameBackwardRuleCache_1121_ = lean_ctor_get(v___x_1117_, 3);
v_frameDB_1122_ = lean_ctor_get(v___x_1117_, 4);
v_invariants_1123_ = lean_ctor_get(v___x_1117_, 5);
v_vcs_1124_ = lean_ctor_get(v___x_1117_, 6);
v_simpState_1125_ = lean_ctor_get(v___x_1117_, 7);
v_fuel_1126_ = lean_ctor_get(v___x_1117_, 8);
v_inlineHandledInvariants_1127_ = lean_ctor_get(v___x_1117_, 9);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1129_ = v___x_1117_;
v_isShared_1130_ = v_isSharedCheck_1143_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_inlineHandledInvariants_1127_);
lean_inc(v_fuel_1126_);
lean_inc(v_simpState_1125_);
lean_inc(v_vcs_1124_);
lean_inc(v_invariants_1123_);
lean_inc(v_frameDB_1122_);
lean_inc(v_frameBackwardRuleCache_1121_);
lean_inc(v_latticeBackwardRuleCache_1120_);
lean_inc(v_splitBackwardRuleCache_1119_);
lean_inc(v_specBackwardRuleCache_1118_);
lean_dec(v___x_1117_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1143_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v_val_1111_);
v___x_1132_ = v___x_1104_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_toGoalState_1100_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_val_1111_);
v___x_1132_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_array_push(v_vcs_1124_, v___x_1132_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 6, v___x_1133_);
v___x_1135_ = v___x_1129_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_specBackwardRuleCache_1118_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_splitBackwardRuleCache_1119_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_latticeBackwardRuleCache_1120_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_frameBackwardRuleCache_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_frameDB_1122_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_invariants_1123_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_simpState_1125_);
lean_ctor_set(v_reuseFailAlloc_1141_, 8, v_fuel_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 9, v_inlineHandledInvariants_1127_);
v___x_1135_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = lean_st_ref_put(v_a_1075_, v___x_1135_);
v___x_1137_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1137_);
v___x_1139_ = v___x_1115_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1111_);
lean_del_object(v___x_1104_);
lean_dec_ref(v_toGoalState_1100_);
return v___x_1113_;
}
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec(v_a_1107_);
lean_del_object(v___x_1104_);
lean_dec_ref(v_toGoalState_1100_);
v___x_1146_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1146_);
v___x_1148_ = v___x_1109_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1104_);
lean_dec_ref(v_toGoalState_1100_);
v_a_1151_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1106_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1106_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_dec_ref(v_toGoalState_1100_);
lean_dec(v_a_1096_);
v___x_1161_ = lean_box(0);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1161_);
v___x_1163_ = v___x_1098_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
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
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1095_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1095_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_del_object(v___x_1089_);
lean_dec_ref(v_toGoalState_1086_);
v_a_1175_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1091_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1091_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object* v_mvarId_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_mctx_1202_; lean_object* v_eAssignment_1203_; uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_mctx_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_mctx_1202_);
lean_dec(v___x_1201_);
v_eAssignment_1203_ = lean_ctor_get(v_mctx_1202_, 8);
lean_inc_ref(v_eAssignment_1203_);
lean_dec_ref(v_mctx_1202_);
v___x_1204_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1203_, v_mvarId_1198_);
lean_dec_ref(v_eAssignment_1203_);
v___x_1205_ = lean_box(v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object* v_mvarId_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec(v_mvarId_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v___x_1211_, lean_object* v_scope_1212_, size_t v_sz_1213_, size_t v_i_1214_, lean_object* v_bs_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_lt(v_i_1214_, v_sz_1213_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v_scope_1212_);
lean_dec_ref(v___x_1211_);
return v_bs_1215_;
}
else
{
lean_object* v_v_1217_; lean_object* v___x_1218_; lean_object* v_bs_x27_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v_v_1217_ = lean_array_uget(v_bs_1215_, v_i_1214_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v_bs_x27_1219_ = lean_array_uset(v_bs_1215_, v_i_1214_, v___x_1218_);
lean_inc_ref(v___x_1211_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1211_);
lean_ctor_set(v___x_1220_, 1, v_v_1217_);
lean_inc_ref(v_scope_1212_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v_scope_1212_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1214_, v___x_1222_);
v___x_1224_ = lean_array_uset(v_bs_x27_1219_, v_i_1214_, v___x_1221_);
v_i_1214_ = v___x_1223_;
v_bs_1215_ = v___x_1224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v___x_1226_, lean_object* v_scope_1227_, lean_object* v_sz_1228_, lean_object* v_i_1229_, lean_object* v_bs_1230_){
_start:
{
size_t v_sz_boxed_1231_; size_t v_i_boxed_1232_; lean_object* v_res_1233_; 
v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1228_);
lean_dec(v_sz_1228_);
v_i_boxed_1232_ = lean_unbox_usize(v_i_1229_);
lean_dec(v_i_1229_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v___x_1226_, v_scope_1227_, v_sz_boxed_1231_, v_i_boxed_1232_, v_bs_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_a_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1247_ = lean_array_get_size(v_a_1234_);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_sub(v___x_1247_, v___x_1248_);
v___x_1250_ = lean_nat_dec_lt(v___x_1249_, v___x_1247_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; 
lean_dec(v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1234_);
return v___x_1251_;
}
else
{
lean_object* v___x_1252_; lean_object* v_goal_1253_; lean_object* v_scope_1254_; lean_object* v_mvarId_1255_; lean_object* v___x_1256_; 
v___x_1252_ = lean_array_fget_borrowed(v_a_1234_, v___x_1249_);
lean_dec(v___x_1249_);
v_goal_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc_ref(v_goal_1253_);
v_scope_1254_ = lean_ctor_get(v___x_1252_, 1);
lean_inc_ref(v_scope_1254_);
v_mvarId_1255_ = lean_ctor_get(v_goal_1253_, 1);
v___x_1256_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1255_, v___y_1243_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = lean_array_pop(v_a_1234_);
v___x_1259_ = lean_unbox(v_a_1257_);
lean_dec(v_a_1257_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1253_, v___y_1235_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_toGoalState_1262_; uint8_t v_inconsistent_1263_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v_toGoalState_1262_ = lean_ctor_get(v_a_1261_, 0);
v_inconsistent_1263_ = lean_ctor_get_uint8(v_toGoalState_1262_, sizeof(void*)*17);
if (v_inconsistent_1263_ == 0)
{
lean_object* v_mvarId_1264_; lean_object* v___x_1265_; 
v_mvarId_1264_ = lean_ctor_get(v_a_1261_, 1);
lean_inc(v_mvarId_1264_);
v___x_1265_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1254_, v_mvarId_1264_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
if (lean_obj_tag(v_a_1266_) == 0)
{
lean_object* v_scope_1267_; lean_object* v_subgoals_1268_; lean_object* v___x_1269_; 
lean_inc_ref(v_toGoalState_1262_);
lean_dec(v_a_1261_);
v_scope_1267_ = lean_ctor_get(v_a_1266_, 0);
lean_inc_ref(v_scope_1267_);
v_subgoals_1268_ = lean_ctor_get(v_a_1266_, 1);
lean_inc(v_subgoals_1268_);
lean_dec_ref_known(v_a_1266_, 2);
v___x_1269_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1268_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v_subgoals_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; size_t v_sz_1272_; size_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = l_Array_reverse___redArg(v_a_1270_);
v_sz_1272_ = lean_array_size(v___x_1271_);
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_toGoalState_1262_, v_scope_1267_, v_sz_1272_, v___x_1273_, v___x_1271_);
v___x_1275_ = l_Array_append___redArg(v___x_1258_, v___x_1274_);
lean_dec_ref(v___x_1274_);
v_a_1234_ = v___x_1275_;
goto _start;
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_scope_1267_);
lean_dec_ref(v_toGoalState_1262_);
lean_dec_ref(v___x_1258_);
v_a_1277_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1269_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1269_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref_known(v_a_1266_, 1);
v___x_1285_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1261_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec_ref_known(v___x_1285_, 1);
v_a_1234_ = v___x_1258_;
goto _start;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v___x_1258_);
v_a_1287_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1285_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1285_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1261_);
lean_dec_ref(v___x_1258_);
v_a_1295_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1265_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1265_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_dec(v_a_1261_);
lean_dec_ref(v_scope_1254_);
v_a_1234_ = v___x_1258_;
goto _start;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_scope_1254_);
v_a_1304_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1260_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1260_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1254_);
lean_dec_ref(v_goal_1253_);
v_a_1234_ = v___x_1258_;
goto _start;
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_scope_1254_);
lean_dec_ref(v_goal_1253_);
lean_dec_ref(v_a_1234_);
v_a_1313_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1256_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1256_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_a_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1335_, lean_object* v_goal_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_toGoalState_1349_; lean_object* v_mvarId_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1389_; 
v_toGoalState_1349_ = lean_ctor_get(v_goal_1336_, 0);
v_mvarId_1350_ = lean_ctor_get(v_goal_1336_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_goal_1336_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1352_ = v_goal_1336_;
v_isShared_1353_ = v_isSharedCheck_1389_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_mvarId_1350_);
lean_inc(v_toGoalState_1349_);
lean_dec(v_goal_1336_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1389_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1350_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v_a_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_toGoalState_1349_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_a_1355_);
v___x_1357_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v_scope_1335_);
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_mk_empty_array_with_capacity(v___x_1359_);
v___x_1361_ = lean_array_push(v___x_1360_, v___x_1358_);
v___x_1362_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v___x_1361_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1371_);
v___x_1364_ = v___x_1362_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v___x_1362_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_box(0);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1362_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1362_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_del_object(v___x_1352_);
lean_dec_ref(v_toGoalState_1349_);
lean_dec_ref(v_scope_1335_);
v_a_1381_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1354_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1354_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1390_, lean_object* v_goal_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1390_, v_goal_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v_mvarId_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1405_, v___y_1414_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v_mvarId_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_mvarId_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v_mvarId_1419_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_inst_1433_, lean_object* v_a_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_inst_1448_, lean_object* v_a_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_inst_1448_, v_a_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_config_1474_; lean_object* v_sharedExprs_1475_; uint8_t v_verbose_1476_; uint8_t v_enforceUnfoldReducible_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_config_1474_ = lean_ctor_get(v___y_1467_, 1);
v_sharedExprs_1475_ = lean_ctor_get(v___y_1467_, 0);
v_verbose_1476_ = lean_ctor_get_uint8(v_config_1474_, 0);
v_enforceUnfoldReducible_1477_ = lean_ctor_get_uint8(v_config_1474_, 1);
v___x_1478_ = 0;
v___x_1479_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_1479_, 0, v_verbose_1476_);
lean_ctor_set_uint8(v___x_1479_, 1, v_enforceUnfoldReducible_1477_);
lean_ctor_set_uint8(v___x_1479_, 2, v___x_1478_);
lean_inc_ref(v_sharedExprs_1475_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_sharedExprs_1475_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc(v___y_1468_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
v___x_1481_ = lean_apply_10(v_x_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___x_1480_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, lean_box(0));
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_1494_, lean_object* v_x_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_1507_, v_x_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_1520_, lean_object* v_scope_1521_, lean_object* v_goal_1522_, lean_object* v_ctx_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_st_mk_ref(v_initState_1520_);
v___x_1535_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1521_, v_goal_1522_, v_ctx_1523_, v___x_1534_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1545_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1545_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = lean_st_ref_get(v___x_1534_);
lean_dec(v___x_1534_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1536_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1541_);
v___x_1543_ = v___x_1538_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v___x_1534_);
v_a_1546_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1535_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1535_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_1554_, lean_object* v_scope_1555_, lean_object* v_goal_1556_, lean_object* v_ctx_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_1554_, v_scope_1555_, v_goal_1556_, v_ctx_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v_ctx_1557_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v_mctx_1573_; lean_object* v_eAssignment_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1572_ = lean_st_ref_get(v___y_1570_);
v_mctx_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_mctx_1573_);
lean_dec(v___x_1572_);
v_eAssignment_1574_ = lean_ctor_get(v_mctx_1573_, 8);
lean_inc_ref(v_eAssignment_1574_);
lean_dec_ref(v_mctx_1573_);
v___x_1575_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1574_, v_mvarId_1569_);
lean_dec_ref(v_eAssignment_1574_);
v___x_1576_ = lean_box(v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec(v_mvarId_1578_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_1582_, size_t v_i_1583_, size_t v_stop_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_a_1597_; uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_eq(v_i_1583_, v_stop_1584_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v_mvarId_1605_; lean_object* v___x_1606_; 
v___x_1602_ = lean_array_uget_borrowed(v_as_1582_, v_i_1583_);
v_mvarId_1605_ = lean_ctor_get(v___x_1602_, 1);
v___x_1606_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1605_, v___y_1592_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; uint8_t v___x_1608_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = lean_unbox(v_a_1607_);
lean_dec(v_a_1607_);
if (v___x_1608_ == 0)
{
goto v___jp_1603_;
}
else
{
v_a_1597_ = v_b_1585_;
goto v___jp_1596_;
}
}
else
{
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1609_; uint8_t v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1610_ = lean_unbox(v_a_1609_);
lean_dec(v_a_1609_);
if (v___x_1610_ == 0)
{
v_a_1597_ = v_b_1585_;
goto v___jp_1596_;
}
else
{
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_b_1585_);
v_a_1611_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1606_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1606_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
v___jp_1603_:
{
lean_object* v___x_1604_; 
lean_inc(v___x_1602_);
v___x_1604_ = lean_array_push(v_b_1585_, v___x_1602_);
v_a_1597_ = v___x_1604_;
goto v___jp_1596_;
}
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v_b_1585_);
return v___x_1619_;
}
v___jp_1596_:
{
size_t v___x_1598_; size_t v___x_1599_; 
v___x_1598_ = ((size_t)1ULL);
v___x_1599_ = lean_usize_add(v_i_1583_, v___x_1598_);
v_i_1583_ = v___x_1599_;
v_b_1585_ = v_a_1597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_1620_, lean_object* v_i_1621_, lean_object* v_stop_1622_, lean_object* v_b_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
size_t v_i_boxed_1634_; size_t v_stop_boxed_1635_; lean_object* v_res_1636_; 
v_i_boxed_1634_ = lean_unbox_usize(v_i_1621_);
lean_dec(v_i_1621_);
v_stop_boxed_1635_ = lean_unbox_usize(v_stop_1622_);
lean_dec(v_stop_1622_);
v_res_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_1620_, v_i_boxed_1634_, v_stop_boxed_1635_, v_b_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v_as_1620_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_1638_, size_t v_i_1639_, lean_object* v_bs_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_usize_dec_lt(v_i_1639_, v_sz_1638_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_bs_1640_);
return v___x_1647_;
}
else
{
lean_object* v_v_1648_; lean_object* v_mvarId_1649_; lean_object* v___x_1650_; 
v_v_1648_ = lean_array_uget_borrowed(v_bs_1640_, v_i_1639_);
v_mvarId_1649_ = lean_ctor_get(v_v_1648_, 1);
lean_inc_n(v_mvarId_1649_, 2);
v___x_1650_ = l_Lean_MVarId_getTag(v_mvarId_1649_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v_bs_x27_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_unsigned_to_nat(0u);
v_bs_x27_1653_ = lean_array_uset(v_bs_1640_, v_i_1639_, v___x_1652_);
v___x_1654_ = lean_usize_to_nat(v_i_1639_);
v___x_1655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = lean_nat_add(v___x_1654_, v___x_1656_);
lean_dec(v___x_1654_);
v___x_1658_ = l_Nat_reprFast(v___x_1657_);
v___x_1659_ = lean_string_append(v___x_1655_, v___x_1658_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = lean_box(0);
v___x_1661_ = l_Lean_Name_str___override(v___x_1660_, v___x_1659_);
v___x_1662_ = l_Lean_Name_eraseMacroScopes(v_a_1651_);
lean_dec(v_a_1651_);
v___x_1663_ = l_Lean_Name_append(v___x_1661_, v___x_1662_);
v___x_1664_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1649_, v___x_1663_, v___y_1642_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = ((size_t)1ULL);
v___x_1667_ = lean_usize_add(v_i_1639_, v___x_1666_);
v___x_1668_ = lean_array_uset(v_bs_x27_1653_, v_i_1639_, v_a_1665_);
v_i_1639_ = v___x_1667_;
v_bs_1640_ = v___x_1668_;
goto _start;
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_bs_x27_1653_);
v_a_1670_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1664_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1664_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_mvarId_1649_);
lean_dec_ref(v_bs_1640_);
v_a_1678_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1650_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1650_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_1686_, lean_object* v_i_1687_, lean_object* v_bs_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1686_);
lean_dec(v_sz_1686_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_1694_, v_i_boxed_1695_, v_bs_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_1698_, size_t v_i_1699_, lean_object* v_bs_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1699_, v_sz_1698_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_bs_1700_);
return v___x_1704_;
}
else
{
lean_object* v_v_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_v_1705_ = lean_array_uget(v_bs_1700_, v_i_1699_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1700_, v_i_1699_, v___x_1706_);
v___x_1708_ = lean_usize_to_nat(v_i_1699_);
v___x_1709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_add(v___x_1708_, v___x_1710_);
lean_dec(v___x_1708_);
v___x_1712_ = l_Nat_reprFast(v___x_1711_);
v___x_1713_ = lean_string_append(v___x_1709_, v___x_1712_);
lean_dec_ref(v___x_1712_);
v___x_1714_ = lean_box(0);
v___x_1715_ = l_Lean_Name_str___override(v___x_1714_, v___x_1713_);
v___x_1716_ = l_Lean_MVarId_setTag___redArg(v_v_1705_, v___x_1715_, v___y_1701_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1699_, v___x_1718_);
v___x_1720_ = lean_array_uset(v_bs_x27_1707_, v_i_1699_, v_a_1717_);
v_i_1699_ = v___x_1719_;
v_bs_1700_ = v___x_1720_;
goto _start;
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_bs_x27_1707_);
v_a_1722_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1716_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1716_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1730_, lean_object* v_i_1731_, lean_object* v_bs_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1730_);
lean_dec(v_sz_1730_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1731_);
lean_dec(v_i_1731_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_1735_, v_i_boxed_1736_, v_bs_1732_, v___y_1733_);
lean_dec(v___y_1733_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_1738_, size_t v_i_1739_, size_t v_stop_1740_, lean_object* v_b_1741_){
_start:
{
lean_object* v___y_1743_; uint8_t v___x_1747_; 
v___x_1747_ = lean_usize_dec_eq(v_i_1739_, v_stop_1740_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; uint8_t v_retired_1749_; 
v___x_1748_ = lean_array_uget_borrowed(v_as_1738_, v_i_1739_);
v_retired_1749_ = lean_ctor_get_uint8(v___x_1748_, sizeof(void*)*4);
if (v_retired_1749_ == 0)
{
lean_object* v_frameStx_1750_; lean_object* v___x_1751_; 
v_frameStx_1750_ = lean_ctor_get(v___x_1748_, 2);
lean_inc(v_frameStx_1750_);
v___x_1751_ = lean_array_push(v_b_1741_, v_frameStx_1750_);
v___y_1743_ = v___x_1751_;
goto v___jp_1742_;
}
else
{
v___y_1743_ = v_b_1741_;
goto v___jp_1742_;
}
}
else
{
return v_b_1741_;
}
v___jp_1742_:
{
size_t v___x_1744_; size_t v___x_1745_; 
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1739_, v___x_1744_);
v_i_1739_ = v___x_1745_;
v_b_1741_ = v___y_1743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_1752_, lean_object* v_i_1753_, lean_object* v_stop_1754_, lean_object* v_b_1755_){
_start:
{
size_t v_i_boxed_1756_; size_t v_stop_boxed_1757_; lean_object* v_res_1758_; 
v_i_boxed_1756_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_stop_boxed_1757_ = lean_unbox_usize(v_stop_1754_);
lean_dec(v_stop_1754_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1752_, v_i_boxed_1756_, v_stop_boxed_1757_, v_b_1755_);
lean_dec_ref(v_as_1752_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_1761_, lean_object* v_start_1762_, lean_object* v_stop_1763_){
_start:
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0));
v___x_1765_ = lean_nat_dec_lt(v_start_1762_, v_stop_1763_);
if (v___x_1765_ == 0)
{
return v___x_1764_;
}
else
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_array_get_size(v_as_1761_);
v___x_1767_ = lean_nat_dec_le(v_stop_1763_, v___x_1766_);
if (v___x_1767_ == 0)
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_lt(v_start_1762_, v___x_1766_);
if (v___x_1768_ == 0)
{
return v___x_1764_;
}
else
{
size_t v___x_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_usize_of_nat(v_start_1762_);
v___x_1770_ = lean_usize_of_nat(v___x_1766_);
v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1761_, v___x_1769_, v___x_1770_, v___x_1764_);
return v___x_1771_;
}
}
else
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_usize_of_nat(v_start_1762_);
v___x_1773_ = lean_usize_of_nat(v_stop_1763_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1761_, v___x_1772_, v___x_1773_, v___x_1764_);
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_1775_, lean_object* v_start_1776_, lean_object* v_stop_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_1775_, v_start_1776_, v_stop_1777_);
lean_dec(v_stop_1777_);
lean_dec(v_start_1776_);
lean_dec_ref(v_as_1775_);
return v_res_1778_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_unsigned_to_nat(16u);
v___x_1781_ = lean_mk_array(v___x_1780_, v___x_1779_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v___x_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
lean_ctor_set(v___x_1790_, 1, v___x_1788_);
lean_ctor_set(v___x_1790_, 2, v___x_1788_);
lean_ctor_set(v___x_1790_, 3, v___x_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_1791_, lean_object* v_ctx_1792_, lean_object* v_scope_1793_, lean_object* v_stepLimit_x3f_1794_, lean_object* v_frameDB_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v_a_1811_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___y_1835_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1833_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1794_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_box(1);
v___y_1835_ = v___x_1881_;
goto v___jp_1834_;
}
else
{
lean_object* v_val_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_val_1882_ = lean_ctor_get(v_stepLimit_x3f_1794_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_stepLimit_x3f_1794_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v_stepLimit_x3f_1794_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_val_1882_);
lean_dec(v_stepLimit_x3f_1794_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 0);
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_val_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v___y_1835_ = v___x_1887_;
goto v___jp_1834_;
}
}
}
v___jp_1807_:
{
lean_object* v_entries_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_entries_1812_ = lean_ctor_get(v___y_1810_, 1);
lean_inc_ref(v_entries_1812_);
lean_dec_ref(v___y_1810_);
v___x_1813_ = lean_array_get_size(v_entries_1812_);
v___x_1814_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_1812_, v___x_1806_, v___x_1813_);
lean_dec_ref(v_entries_1812_);
v___x_1815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1815_, 0, v___y_1808_);
lean_ctor_set(v___x_1815_, 1, v_a_1811_);
lean_ctor_set(v___x_1815_, 2, v___y_1809_);
lean_ctor_set(v___x_1815_, 3, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
v___jp_1817_:
{
if (lean_obj_tag(v___y_1821_) == 0)
{
lean_object* v_a_1822_; 
v_a_1822_ = lean_ctor_get(v___y_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___y_1821_, 1);
v___y_1808_ = v___y_1818_;
v___y_1809_ = v___y_1819_;
v___y_1810_ = v___y_1820_;
v_a_1811_ = v_a_1822_;
goto v___jp_1807_;
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec_ref(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v___y_1818_);
v_a_1823_ = lean_ctor_get(v___y_1821_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___y_1821_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___y_1821_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___y_1821_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
v___jp_1834_:
{
lean_object* v_initState_1836_; lean_object* v___f_1837_; lean_object* v___x_1838_; 
v_initState_1836_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_initState_1836_, 0, v___x_1831_);
lean_ctor_set(v_initState_1836_, 1, v___x_1831_);
lean_ctor_set(v_initState_1836_, 2, v___x_1831_);
lean_ctor_set(v_initState_1836_, 3, v___x_1831_);
lean_ctor_set(v_initState_1836_, 4, v_frameDB_1795_);
lean_ctor_set(v_initState_1836_, 5, v___x_1832_);
lean_ctor_set(v_initState_1836_, 6, v___x_1832_);
lean_ctor_set(v_initState_1836_, 7, v___x_1833_);
lean_ctor_set(v_initState_1836_, 8, v___y_1835_);
lean_ctor_set(v_initState_1836_, 9, v___x_1831_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1837_, 0, v_initState_1836_);
lean_closure_set(v___f_1837_, 1, v_scope_1793_);
lean_closure_set(v___f_1837_, 2, v_goal_1791_);
lean_closure_set(v___f_1837_, 3, v_ctx_1792_);
v___x_1838_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_1837_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_snd_1840_; lean_object* v_frameDB_1841_; lean_object* v_invariants_1842_; lean_object* v_vcs_1843_; lean_object* v_inlineHandledInvariants_1844_; size_t v_sz_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v_snd_1840_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_a_1839_);
v_frameDB_1841_ = lean_ctor_get(v_snd_1840_, 4);
lean_inc_ref(v_frameDB_1841_);
v_invariants_1842_ = lean_ctor_get(v_snd_1840_, 5);
lean_inc_ref_n(v_invariants_1842_, 2);
v_vcs_1843_ = lean_ctor_get(v_snd_1840_, 6);
lean_inc_ref(v_vcs_1843_);
v_inlineHandledInvariants_1844_ = lean_ctor_get(v_snd_1840_, 9);
lean_inc_ref(v_inlineHandledInvariants_1844_);
lean_dec(v_snd_1840_);
v_sz_1845_ = lean_array_size(v_invariants_1842_);
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1845_, v___x_1846_, v_invariants_1842_, v_a_1802_);
if (lean_obj_tag(v___x_1847_) == 0)
{
size_t v_sz_1848_; lean_object* v___x_1849_; 
lean_dec_ref_known(v___x_1847_, 1);
v_sz_1848_ = lean_array_size(v_vcs_1843_);
lean_inc_ref(v_vcs_1843_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1848_, v___x_1846_, v_vcs_1843_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
lean_dec_ref_known(v___x_1849_, 1);
v___x_1850_ = lean_array_get_size(v_vcs_1843_);
v___x_1851_ = lean_nat_dec_lt(v___x_1806_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec_ref(v_vcs_1843_);
v___y_1808_ = v_invariants_1842_;
v___y_1809_ = v_inlineHandledInvariants_1844_;
v___y_1810_ = v_frameDB_1841_;
v_a_1811_ = v___x_1832_;
goto v___jp_1807_;
}
else
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_nat_dec_le(v___x_1850_, v___x_1850_);
if (v___x_1852_ == 0)
{
if (v___x_1851_ == 0)
{
lean_dec_ref(v_vcs_1843_);
v___y_1808_ = v_invariants_1842_;
v___y_1809_ = v_inlineHandledInvariants_1844_;
v___y_1810_ = v_frameDB_1841_;
v_a_1811_ = v___x_1832_;
goto v___jp_1807_;
}
else
{
size_t v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_usize_of_nat(v___x_1850_);
v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1843_, v___x_1846_, v___x_1853_, v___x_1832_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec_ref(v_vcs_1843_);
v___y_1818_ = v_invariants_1842_;
v___y_1819_ = v_inlineHandledInvariants_1844_;
v___y_1820_ = v_frameDB_1841_;
v___y_1821_ = v___x_1854_;
goto v___jp_1817_;
}
}
else
{
size_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_usize_of_nat(v___x_1850_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1843_, v___x_1846_, v___x_1855_, v___x_1832_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec_ref(v_vcs_1843_);
v___y_1818_ = v_invariants_1842_;
v___y_1819_ = v_inlineHandledInvariants_1844_;
v___y_1820_ = v_frameDB_1841_;
v___y_1821_ = v___x_1856_;
goto v___jp_1817_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_inlineHandledInvariants_1844_);
lean_dec_ref(v_vcs_1843_);
lean_dec_ref(v_invariants_1842_);
lean_dec_ref(v_frameDB_1841_);
v_a_1857_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1849_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1849_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v_inlineHandledInvariants_1844_);
lean_dec_ref(v_vcs_1843_);
lean_dec_ref(v_invariants_1842_);
lean_dec_ref(v_frameDB_1841_);
v_a_1865_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1847_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1847_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1838_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1838_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_1890_, lean_object* v_ctx_1891_, lean_object* v_scope_1892_, lean_object* v_stepLimit_x3f_1893_, lean_object* v_frameDB_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_1890_, v_ctx_1891_, v_scope_1892_, v_stepLimit_x3f_1893_, v_frameDB_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1906_, v___y_1913_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v_mvarId_1918_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_1930_, size_t v_sz_1931_, size_t v_i_1932_, lean_object* v_bs_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1931_, v_i_1932_, v_bs_1933_, v___y_1940_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_bs_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_1945_, v_sz_boxed_1959_, v_i_boxed_1960_, v_bs_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v_as_1945_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_1962_, size_t v_sz_1963_, size_t v_i_1964_, lean_object* v_bs_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1963_, v_i_1964_, v_bs_1965_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_1977_, lean_object* v_sz_1978_, lean_object* v_i_1979_, lean_object* v_bs_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
size_t v_sz_boxed_1991_; size_t v_i_boxed_1992_; lean_object* v_res_1993_; 
v_sz_boxed_1991_ = lean_unbox_usize(v_sz_1978_);
lean_dec(v_sz_1978_);
v_i_boxed_1992_ = lean_unbox_usize(v_i_1979_);
lean_dec(v_i_1979_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_1977_, v_sz_boxed_1991_, v_i_boxed_1992_, v_bs_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v_as_1977_);
return v_res_1993_;
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
