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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Array_mkArray0___redArg();
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
v___x_70_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_14530__boxed_174_; size_t v_x_14531__boxed_175_; lean_object* v_res_176_; 
v_x_14530__boxed_174_ = lean_unbox_usize(v_x_170_);
lean_dec(v_x_170_);
v_x_14531__boxed_175_ = lean_unbox_usize(v_x_171_);
lean_dec(v_x_171_);
v_res_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_169_, v_x_14530__boxed_174_, v_x_14531__boxed_175_, v_x_172_, v_x_173_);
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
lean_object* v___x_188_; lean_object* v_mctx_189_; lean_object* v_cache_190_; lean_object* v_zetaDeltaFVarIds_191_; lean_object* v_postponed_192_; lean_object* v_diag_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_223_; 
v___x_188_ = lean_st_ref_take(v___y_186_);
v_mctx_189_ = lean_ctor_get(v___x_188_, 0);
v_cache_190_ = lean_ctor_get(v___x_188_, 1);
v_zetaDeltaFVarIds_191_ = lean_ctor_get(v___x_188_, 2);
v_postponed_192_ = lean_ctor_get(v___x_188_, 3);
v_diag_193_ = lean_ctor_get(v___x_188_, 4);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_223_ == 0)
{
v___x_195_ = v___x_188_;
v_isShared_196_ = v_isSharedCheck_223_;
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
v_isShared_196_ = v_isSharedCheck_223_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_depth_197_; lean_object* v_levelAssignDepth_198_; lean_object* v_lmvarCounter_199_; lean_object* v_mvarCounter_200_; lean_object* v_lDecls_201_; lean_object* v_decls_202_; lean_object* v_userNames_203_; lean_object* v_lAssignment_204_; lean_object* v_eAssignment_205_; lean_object* v_dAssignment_206_; lean_object* v_instanceTypedMVars_207_; lean_object* v_synthNormMemo_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_222_; 
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
v_synthNormMemo_208_ = lean_ctor_get(v_mctx_189_, 11);
v_isSharedCheck_222_ = !lean_is_exclusive(v_mctx_189_);
if (v_isSharedCheck_222_ == 0)
{
v___x_210_ = v_mctx_189_;
v_isShared_211_ = v_isSharedCheck_222_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_synthNormMemo_208_);
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
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_222_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = lean_box(0);
v___x_213_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_205_, v_mvarId_184_, v_val_185_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 8, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_depth_197_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_levelAssignDepth_198_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_lmvarCounter_199_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v_mvarCounter_200_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_lDecls_201_);
lean_ctor_set(v_reuseFailAlloc_221_, 5, v_decls_202_);
lean_ctor_set(v_reuseFailAlloc_221_, 6, v_userNames_203_);
lean_ctor_set(v_reuseFailAlloc_221_, 7, v_lAssignment_204_);
lean_ctor_set(v_reuseFailAlloc_221_, 8, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_221_, 9, v_dAssignment_206_);
lean_ctor_set(v_reuseFailAlloc_221_, 10, v_instanceTypedMVars_207_);
lean_ctor_set(v_reuseFailAlloc_221_, 11, v_synthNormMemo_208_);
v___x_215_ = v_reuseFailAlloc_221_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_217_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_215_);
v___x_217_ = v___x_195_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_cache_190_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_zetaDeltaFVarIds_191_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_postponed_192_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_diag_193_);
v___x_217_ = v_reuseFailAlloc_220_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_st_ref_put(v___y_186_, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_212_);
return v___x_219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_224_, lean_object* v_val_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_224_, v_val_225_, v___y_226_);
lean_dec(v___y_226_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_keys_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_array_get_size(v_keys_229_);
v___x_233_ = lean_nat_dec_lt(v_i_230_, v___x_232_);
if (v___x_233_ == 0)
{
lean_dec(v_i_230_);
return v___x_233_;
}
else
{
lean_object* v_k_x27_234_; uint8_t v___x_235_; 
v_k_x27_234_ = lean_array_fget_borrowed(v_keys_229_, v_i_230_);
v___x_235_ = l_Lean_instBEqMVarId_beq(v_k_231_, v_k_x27_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_i_230_, v___x_236_);
lean_dec(v_i_230_);
v_i_230_ = v___x_237_;
goto _start;
}
else
{
lean_dec(v_i_230_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_keys_239_, lean_object* v_i_240_, lean_object* v_k_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_239_, v_i_240_, v_k_241_);
lean_dec(v_k_241_);
lean_dec_ref(v_keys_239_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_244_, size_t v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v_es_247_; lean_object* v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v_j_251_; lean_object* v___x_252_; 
v_es_247_ = lean_ctor_get(v_x_244_, 0);
v___x_248_ = lean_box(2);
v___x_249_ = ((size_t)31ULL);
v___x_250_ = lean_usize_land(v_x_245_, v___x_249_);
v_j_251_ = lean_usize_to_nat(v___x_250_);
v___x_252_ = lean_array_get_borrowed(v___x_248_, v_es_247_, v_j_251_);
lean_dec(v_j_251_);
switch(lean_obj_tag(v___x_252_))
{
case 0:
{
lean_object* v_key_253_; uint8_t v___x_254_; 
v_key_253_ = lean_ctor_get(v___x_252_, 0);
v___x_254_ = l_Lean_instBEqMVarId_beq(v_x_246_, v_key_253_);
return v___x_254_;
}
case 1:
{
lean_object* v_node_255_; size_t v___x_256_; size_t v___x_257_; 
v_node_255_ = lean_ctor_get(v___x_252_, 0);
v___x_256_ = ((size_t)5ULL);
v___x_257_ = lean_usize_shift_right(v_x_245_, v___x_256_);
v_x_244_ = v_node_255_;
v_x_245_ = v___x_257_;
goto _start;
}
default: 
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
}
else
{
lean_object* v_ks_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_ks_260_ = lean_ctor_get(v_x_244_, 0);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_260_, v___x_261_, v_x_246_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
size_t v_x_14752__boxed_266_; uint8_t v_res_267_; lean_object* v_r_268_; 
v_x_14752__boxed_266_ = lean_unbox_usize(v_x_264_);
lean_dec(v_x_264_);
v_res_267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_263_, v_x_14752__boxed_266_, v_x_265_);
lean_dec(v_x_265_);
lean_dec_ref(v_x_263_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
uint64_t v___x_271_; size_t v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_instHashableMVarId_hash(v_x_270_);
v___x_272_ = lean_uint64_to_usize(v___x_271_);
v___x_273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_269_, v___x_272_, v_x_270_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_274_, v_x_275_);
lean_dec(v_x_275_);
lean_dec_ref(v_x_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; lean_object* v_mctx_282_; lean_object* v_eAssignment_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = lean_st_ref_get(v___y_279_);
v_mctx_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_mctx_282_);
lean_dec(v___x_281_);
v_eAssignment_283_ = lean_ctor_get(v_mctx_282_, 8);
lean_inc_ref(v_eAssignment_283_);
lean_dec_ref(v_mctx_282_);
v___x_284_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_283_, v_mvarId_278_);
lean_dec_ref(v_eAssignment_283_);
v___x_285_ = lean_box(v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec(v_mvarId_287_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object* v___f_302_, lean_object* v_mv_303_, lean_object* v_val_304_, lean_object* v_tac_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___y_322_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_toCold_368_; lean_object* v_currRecDepth_369_; lean_object* v_ref_370_; uint16_t v_optionFlags_371_; uint8_t v_suppressElabErrors_372_; uint8_t v_isRecordingDeps_373_; lean_object* v___x_374_; uint8_t v_transparency_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v_ref_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_313_ = lean_box(0);
v___x_314_ = lean_box(0);
v___x_315_ = 1;
v___x_319_ = lean_box(1);
v___x_320_ = 0;
v___x_366_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2));
v___x_367_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_367_, 0, v___x_313_);
lean_ctor_set(v___x_367_, 1, v___x_314_);
lean_ctor_set(v___x_367_, 2, v___x_313_);
lean_ctor_set(v___x_367_, 3, v___f_302_);
lean_ctor_set(v___x_367_, 4, v___x_319_);
lean_ctor_set(v___x_367_, 5, v___x_319_);
lean_ctor_set(v___x_367_, 6, v___x_313_);
lean_ctor_set(v___x_367_, 7, v___x_366_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8, v___x_315_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 1, v___x_315_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 2, v___x_315_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 3, v___x_315_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 4, v___x_320_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 5, v___x_320_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 6, v___x_320_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 7, v___x_320_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 8, v___x_315_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 9, v___x_320_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 10, v___x_315_);
v_toCold_368_ = lean_ctor_get(v___y_310_, 0);
v_currRecDepth_369_ = lean_ctor_get(v___y_310_, 1);
v_ref_370_ = lean_ctor_get(v___y_310_, 2);
v_optionFlags_371_ = lean_ctor_get_uint16(v___y_310_, sizeof(void*)*3);
v_suppressElabErrors_372_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*3 + 2);
v_isRecordingDeps_373_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*3 + 3);
v___x_374_ = l_Lean_Meta_Context_config(v___y_308_);
v_transparency_375_ = lean_ctor_get_uint8(v___x_374_, 9);
lean_dec_ref(v___x_374_);
v___x_376_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3));
v___x_377_ = 1;
v_ref_378_ = l_Lean_replaceRef(v_val_304_, v_ref_370_);
lean_inc(v_currRecDepth_369_);
lean_inc_ref(v_toCold_368_);
v___x_379_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_379_, 0, v_toCold_368_);
lean_ctor_set(v___x_379_, 1, v_currRecDepth_369_);
lean_ctor_set(v___x_379_, 2, v_ref_378_);
lean_ctor_set_uint16(v___x_379_, sizeof(void*)*3, v_optionFlags_371_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 2, v_suppressElabErrors_372_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*3 + 3, v_isRecordingDeps_373_);
v___x_380_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_375_, v___x_377_);
if (v___x_380_ == 0)
{
lean_object* v_keyedConfig_381_; uint8_t v_trackZetaDelta_382_; lean_object* v_zetaDeltaSet_383_; lean_object* v_lctx_384_; lean_object* v_localInstances_385_; lean_object* v_defEqCtx_x3f_386_; lean_object* v_synthPendingDepth_387_; lean_object* v_customCanUnfoldPredicate_x3f_388_; uint8_t v_univApprox_389_; uint8_t v_inTypeClassResolution_390_; uint8_t v_cacheInferType_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_keyedConfig_381_ = lean_ctor_get(v___y_308_, 0);
v_trackZetaDelta_382_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7);
v_zetaDeltaSet_383_ = lean_ctor_get(v___y_308_, 1);
v_lctx_384_ = lean_ctor_get(v___y_308_, 2);
v_localInstances_385_ = lean_ctor_get(v___y_308_, 3);
v_defEqCtx_x3f_386_ = lean_ctor_get(v___y_308_, 4);
v_synthPendingDepth_387_ = lean_ctor_get(v___y_308_, 5);
v_customCanUnfoldPredicate_x3f_388_ = lean_ctor_get(v___y_308_, 6);
v_univApprox_389_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_390_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 2);
v_cacheInferType_391_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_381_);
v___x_392_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_377_, v_keyedConfig_381_);
lean_inc(v_customCanUnfoldPredicate_x3f_388_);
lean_inc(v_synthPendingDepth_387_);
lean_inc(v_defEqCtx_x3f_386_);
lean_inc_ref(v_localInstances_385_);
lean_inc_ref(v_lctx_384_);
lean_inc(v_zetaDeltaSet_383_);
v___x_393_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_zetaDeltaSet_383_);
lean_ctor_set(v___x_393_, 2, v_lctx_384_);
lean_ctor_set(v___x_393_, 3, v_localInstances_385_);
lean_ctor_set(v___x_393_, 4, v_defEqCtx_x3f_386_);
lean_ctor_set(v___x_393_, 5, v_synthPendingDepth_387_);
lean_ctor_set(v___x_393_, 6, v_customCanUnfoldPredicate_x3f_388_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*7, v_trackZetaDelta_382_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*7 + 1, v_univApprox_389_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*7 + 2, v_inTypeClassResolution_390_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*7 + 3, v_cacheInferType_391_);
lean_inc(v_mv_303_);
v___x_394_ = l_Lean_Elab_runTactic(v_mv_303_, v_tac_305_, v___x_367_, v___x_376_, v___x_393_, v___y_309_, v___x_379_, v___y_311_);
lean_dec_ref_known(v___x_379_, 3);
lean_dec_ref_known(v___x_393_, 7);
v___y_322_ = v___x_394_;
goto v___jp_321_;
}
else
{
lean_object* v___x_395_; 
lean_inc(v_mv_303_);
v___x_395_ = l_Lean_Elab_runTactic(v_mv_303_, v_tac_305_, v___x_367_, v___x_376_, v___y_308_, v___y_309_, v___x_379_, v___y_311_);
lean_dec_ref_known(v___x_379_, 3);
v___y_322_ = v___x_395_;
goto v___jp_321_;
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0));
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
v___jp_321_:
{
if (lean_obj_tag(v___y_322_) == 0)
{
lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref_known(v___y_322_, 1);
v___x_323_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mv_303_, v___y_309_);
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
lean_dec(v_mv_303_);
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
v___x_333_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mv_303_, v___y_309_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
if (lean_obj_tag(v_a_334_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_336_; 
v_val_335_ = lean_ctor_get(v_a_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v_a_334_, 1);
v___x_336_ = l_Lean_Meta_Sym_unfoldReducible(v_val_335_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = l_Lean_Meta_Sym_shareCommon(v_a_337_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v___x_340_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mv_303_, v_a_339_, v___y_309_);
lean_dec_ref(v___x_340_);
goto v___jp_316_;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_mv_303_);
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
lean_dec(v_mv_303_);
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
lean_dec(v_mv_303_);
goto v___jp_316_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_mv_303_);
v_a_358_ = lean_ctor_get(v___y_322_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___y_322_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___y_322_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___y_322_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_396_, lean_object* v_mv_397_, lean_object* v_val_398_, lean_object* v_tac_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_396_, v_mv_397_, v_val_398_, v_tac_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v_val_398_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v_key_411_; lean_object* v_value_412_; lean_object* v_tail_413_; uint8_t v___x_414_; 
v_key_411_ = lean_ctor_get(v_x_409_, 0);
v_value_412_ = lean_ctor_get(v_x_409_, 1);
v_tail_413_ = lean_ctor_get(v_x_409_, 2);
v___x_414_ = lean_nat_dec_eq(v_key_411_, v_a_408_);
if (v___x_414_ == 0)
{
v_x_409_ = v_tail_413_;
goto _start;
}
else
{
lean_object* v___x_416_; 
lean_inc(v_value_412_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_value_412_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_417_, v_x_418_);
lean_dec(v_x_418_);
lean_dec(v_a_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_buckets_422_; lean_object* v___x_423_; uint64_t v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v_fold_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_buckets_422_ = lean_ctor_get(v_m_420_, 1);
v___x_423_ = lean_array_get_size(v_buckets_422_);
v___x_424_ = lean_uint64_of_nat(v_a_421_);
v___x_425_ = 32ULL;
v___x_426_ = lean_uint64_shift_right(v___x_424_, v___x_425_);
v_fold_427_ = lean_uint64_xor(v___x_424_, v___x_426_);
v___x_428_ = 16ULL;
v___x_429_ = lean_uint64_shift_right(v_fold_427_, v___x_428_);
v___x_430_ = lean_uint64_xor(v_fold_427_, v___x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = lean_usize_of_nat(v___x_423_);
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_sub(v___x_432_, v___x_433_);
v___x_435_ = lean_usize_land(v___x_431_, v___x_434_);
v___x_436_ = lean_array_uget_borrowed(v_buckets_422_, v___x_435_);
v___x_437_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_421_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_m_438_);
return v_res_440_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Array_mkArray0___redArg();
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object* v_invariantAlts_505_, lean_object* v_n_506_, lean_object* v_mv_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___y_516_; lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_505_, v_n_506_);
if (lean_obj_tag(v___x_543_) == 1)
{
lean_object* v_val_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_615_; 
v_val_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_615_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_615_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_val_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_615_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___f_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___f_548_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0));
v___x_549_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5));
lean_inc(v_val_544_);
v___x_550_ = l_Lean_Syntax_isOfKind(v_val_544_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7));
lean_inc(v_val_544_);
v___x_552_ = l_Lean_Syntax_isOfKind(v_val_544_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_555_; 
lean_dec(v_val_544_);
lean_dec(v_mv_507_);
v___x_553_ = lean_box(v___x_552_);
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
lean_ctor_set(v___x_546_, 0, v___x_553_);
v___x_555_ = v___x_546_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = l_Lean_Syntax_getArg(v_val_544_, v___x_557_);
v___x_559_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9));
lean_inc(v___x_558_);
v___x_560_ = l_Lean_Syntax_isOfKind(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_563_; 
lean_dec(v___x_558_);
lean_dec(v_val_544_);
lean_dec(v_mv_507_);
v___x_561_ = lean_box(v___x_560_);
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
lean_ctor_set(v___x_546_, 0, v___x_561_);
v___x_563_ = v___x_546_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
else
{
lean_object* v_ref_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_args_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_del_object(v___x_546_);
v_ref_565_ = lean_ctor_get(v_a_512_, 2);
v___x_566_ = l_Lean_Syntax_getArg(v___x_558_, v___x_557_);
lean_dec(v___x_558_);
v___x_567_ = lean_unsigned_to_nat(3u);
v___x_568_ = l_Lean_Syntax_getArg(v_val_544_, v___x_567_);
v_args_569_ = l_Lean_Syntax_getArgs(v___x_566_);
lean_dec(v___x_566_);
v___x_570_ = l_Lean_SourceInfo_fromRef(v_ref_565_, v___x_550_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11));
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_570_, 11);
v___x_573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_570_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14));
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16));
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18));
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20));
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21));
v___x_579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_570_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22);
v___x_581_ = l_Array_append___redArg(v___x_580_, v_args_569_);
lean_dec_ref(v_args_569_);
v___x_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_582_, 0, v___x_570_);
lean_ctor_set(v___x_582_, 1, v___x_576_);
lean_ctor_set(v___x_582_, 2, v___x_581_);
v___x_583_ = l_Lean_Syntax_node2(v___x_570_, v___x_577_, v___x_579_, v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23));
v___x_585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_570_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_587_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_570_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
v___x_589_ = l_Lean_Syntax_node2(v___x_570_, v___x_587_, v___x_588_, v___x_568_);
v___x_590_ = l_Lean_Syntax_node3(v___x_570_, v___x_576_, v___x_583_, v___x_585_, v___x_589_);
v___x_591_ = l_Lean_Syntax_node1(v___x_570_, v___x_575_, v___x_590_);
v___x_592_ = l_Lean_Syntax_node1(v___x_570_, v___x_574_, v___x_591_);
v___x_593_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26));
v___x_594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_570_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_Syntax_node3(v___x_570_, v___x_571_, v___x_573_, v___x_592_, v___x_594_);
v___x_596_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_548_, v_mv_507_, v_val_544_, v___x_595_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_val_544_);
v___y_516_ = v___x_596_;
goto v___jp_515_;
}
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = l_Lean_Syntax_getArg(v_val_544_, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28));
v___x_600_ = l_Lean_Syntax_isOfKind(v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec(v_val_544_);
lean_dec(v_mv_507_);
v___x_601_ = lean_box(v___x_600_);
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 0);
lean_ctor_set(v___x_546_, 0, v___x_601_);
v___x_603_ = v___x_546_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v_ref_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_del_object(v___x_546_);
v_ref_605_ = lean_ctor_get(v_a_512_, 2);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = l_Lean_Syntax_getArg(v_val_544_, v___x_606_);
v___x_608_ = 0;
v___x_609_ = l_Lean_SourceInfo_fromRef(v_ref_605_, v___x_608_);
v___x_610_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
lean_inc(v___x_609_);
v___x_612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_609_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
v___x_613_ = l_Lean_Syntax_node2(v___x_609_, v___x_611_, v___x_612_, v___x_607_);
v___x_614_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_548_, v_mv_507_, v_val_544_, v___x_613_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_val_544_);
v___y_516_ = v___x_614_;
goto v___jp_515_;
}
}
}
}
else
{
uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v___x_543_);
lean_dec(v_mv_507_);
v___x_616_ = 0;
v___x_617_ = lean_box(v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
v___jp_515_:
{
if (lean_obj_tag(v___y_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_a_517_ = lean_ctor_get(v___y_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___y_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___y_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___y_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_a_521_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v_a_517_, 0);
lean_inc(v_a_521_);
lean_dec(v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v_a_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_542_; 
v_a_526_ = lean_ctor_get(v___y_516_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___y_516_);
if (v_isSharedCheck_542_ == 0)
{
v___x_528_ = v___y_516_;
v_isShared_529_ = v_isSharedCheck_542_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___y_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_542_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
uint8_t v___x_530_; 
v___x_530_ = l_Lean_Exception_isInterrupt(v_a_526_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
lean_inc(v_a_526_);
v___x_531_ = l_Lean_Exception_isRuntime(v_a_526_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec(v_a_526_);
v___x_532_ = lean_box(v___x_531_);
if (v_isShared_529_ == 0)
{
lean_ctor_set_tag(v___x_528_, 0);
lean_ctor_set(v___x_528_, 0, v___x_532_);
v___x_534_ = v___x_528_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v___x_537_; 
if (v_isShared_529_ == 0)
{
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_526_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
lean_object* v___x_540_; 
if (v_isShared_529_ == 0)
{
v___x_540_ = v___x_528_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_526_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_619_, lean_object* v_n_620_, lean_object* v_mv_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_619_, v_n_620_, v_mv_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_n_620_);
lean_dec_ref(v_invariantAlts_619_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_630_, lean_object* v_m_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_631_, v_a_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_634_, lean_object* v_m_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(v_00_u03b2_634_, v_m_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_m_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_638_, v___y_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_mvarId_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v_mvarId_647_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_656_, lean_object* v_val_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_656_, v_val_657_, v___y_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_666_, lean_object* v_val_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_666_, v_val_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_676_, lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_680_, lean_object* v_a_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_680_, v_a_681_, v_x_682_);
lean_dec(v_x_682_);
lean_dec(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_688_, v_x_689_, v_x_690_);
lean_dec(v_x_690_);
lean_dec_ref(v_x_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_694_, v_x_695_, v_x_696_);
return v___x_697_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_698_, lean_object* v_x_699_, size_t v_x_700_, lean_object* v_x_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_699_, v_x_700_, v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
size_t v_x_15542__boxed_707_; uint8_t v_res_708_; lean_object* v_r_709_; 
v_x_15542__boxed_707_ = lean_unbox_usize(v_x_705_);
lean_dec(v_x_705_);
v_res_708_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_703_, v_x_704_, v_x_15542__boxed_707_, v_x_706_);
lean_dec(v_x_706_);
lean_dec_ref(v_x_704_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_710_, lean_object* v_x_711_, size_t v_x_712_, size_t v_x_713_, lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_711_, v_x_712_, v_x_713_, v_x_714_, v_x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
size_t v_x_15553__boxed_723_; size_t v_x_15554__boxed_724_; lean_object* v_res_725_; 
v_x_15553__boxed_723_ = lean_unbox_usize(v_x_719_);
lean_dec(v_x_719_);
v_x_15554__boxed_724_ = lean_unbox_usize(v_x_720_);
lean_dec(v_x_720_);
v_res_725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_717_, v_x_718_, v_x_15553__boxed_723_, v_x_15554__boxed_724_, v_x_721_, v_x_722_);
return v_res_725_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_726_, lean_object* v_keys_727_, lean_object* v_vals_728_, lean_object* v_heq_729_, lean_object* v_i_730_, lean_object* v_k_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_727_, v_i_730_, v_k_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_733_, lean_object* v_keys_734_, lean_object* v_vals_735_, lean_object* v_heq_736_, lean_object* v_i_737_, lean_object* v_k_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_733_, v_keys_734_, v_vals_735_, v_heq_736_, v_i_737_, v_k_738_);
lean_dec(v_k_738_);
lean_dec_ref(v_vals_735_);
lean_dec_ref(v_keys_734_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_741_, lean_object* v_n_742_, lean_object* v_k_743_, lean_object* v_v_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_742_, v_k_743_, v_v_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_746_, size_t v_depth_747_, lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_heq_750_, lean_object* v_i_751_, lean_object* v_entries_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_747_, v_keys_748_, v_vals_749_, v_i_751_, v_entries_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_754_, lean_object* v_depth_755_, lean_object* v_keys_756_, lean_object* v_vals_757_, lean_object* v_heq_758_, lean_object* v_i_759_, lean_object* v_entries_760_){
_start:
{
size_t v_depth_boxed_761_; lean_object* v_res_762_; 
v_depth_boxed_761_ = lean_unbox_usize(v_depth_755_);
lean_dec(v_depth_755_);
v_res_762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_754_, v_depth_boxed_761_, v_keys_756_, v_vals_757_, v_heq_758_, v_i_759_, v_entries_760_);
lean_dec_ref(v_vals_757_);
lean_dec_ref(v_keys_756_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_764_, v_x_765_, v_x_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
return v_x_769_;
}
else
{
lean_object* v_key_771_; lean_object* v_value_772_; lean_object* v_tail_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_796_; 
v_key_771_ = lean_ctor_get(v_x_770_, 0);
v_value_772_ = lean_ctor_get(v_x_770_, 1);
v_tail_773_ = lean_ctor_get(v_x_770_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_796_ == 0)
{
v___x_775_ = v_x_770_;
v_isShared_776_ = v_isSharedCheck_796_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_tail_773_);
lean_inc(v_value_772_);
lean_inc(v_key_771_);
lean_dec(v_x_770_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_796_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; uint64_t v___x_778_; uint64_t v___x_779_; uint64_t v___x_780_; uint64_t v_fold_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_777_ = lean_array_get_size(v_x_769_);
v___x_778_ = lean_uint64_of_nat(v_key_771_);
v___x_779_ = 32ULL;
v___x_780_ = lean_uint64_shift_right(v___x_778_, v___x_779_);
v_fold_781_ = lean_uint64_xor(v___x_778_, v___x_780_);
v___x_782_ = 16ULL;
v___x_783_ = lean_uint64_shift_right(v_fold_781_, v___x_782_);
v___x_784_ = lean_uint64_xor(v_fold_781_, v___x_783_);
v___x_785_ = lean_uint64_to_usize(v___x_784_);
v___x_786_ = lean_usize_of_nat(v___x_777_);
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_sub(v___x_786_, v___x_787_);
v___x_789_ = lean_usize_land(v___x_785_, v___x_788_);
v___x_790_ = lean_array_uget_borrowed(v_x_769_, v___x_789_);
lean_inc(v___x_790_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 2, v___x_790_);
v___x_792_ = v___x_775_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_key_771_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_value_772_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v___x_790_);
v___x_792_ = v_reuseFailAlloc_795_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; 
v___x_793_ = lean_array_uset(v_x_769_, v___x_789_, v___x_792_);
v_x_769_ = v___x_793_;
v_x_770_ = v_tail_773_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_797_, lean_object* v_source_798_, lean_object* v_target_799_){
_start:
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_array_get_size(v_source_798_);
v___x_801_ = lean_nat_dec_lt(v_i_797_, v___x_800_);
if (v___x_801_ == 0)
{
lean_dec_ref(v_source_798_);
lean_dec(v_i_797_);
return v_target_799_;
}
else
{
lean_object* v_es_802_; lean_object* v___x_803_; lean_object* v_source_804_; lean_object* v_target_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_es_802_ = lean_array_fget(v_source_798_, v_i_797_);
v___x_803_ = lean_box(0);
v_source_804_ = lean_array_fset(v_source_798_, v_i_797_, v___x_803_);
v_target_805_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_799_, v_es_802_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_i_797_, v___x_806_);
lean_dec(v_i_797_);
v_i_797_ = v___x_807_;
v_source_798_ = v_source_804_;
v_target_799_ = v_target_805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_nbuckets_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_810_ = lean_array_get_size(v_data_809_);
v___x_811_ = lean_unsigned_to_nat(2u);
v_nbuckets_812_ = lean_nat_mul(v___x_810_, v___x_811_);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_box(0);
v___x_815_ = lean_mk_array(v_nbuckets_812_, v___x_814_);
v___x_816_ = lean_array_propagate_mark(v_data_809_, v___x_815_);
v___x_817_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_813_, v_data_809_, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
else
{
lean_object* v_key_821_; lean_object* v_tail_822_; uint8_t v___x_823_; 
v_key_821_ = lean_ctor_get(v_x_819_, 0);
v_tail_822_ = lean_ctor_get(v_x_819_, 2);
v___x_823_ = lean_nat_dec_eq(v_key_821_, v_a_818_);
if (v___x_823_ == 0)
{
v_x_819_ = v_tail_822_;
goto _start;
}
else
{
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_829_, lean_object* v_a_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_size_832_; lean_object* v_buckets_833_; lean_object* v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v_fold_838_; uint64_t v___x_839_; uint64_t v___x_840_; uint64_t v___x_841_; size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v_bkt_847_; uint8_t v___x_848_; 
v_size_832_ = lean_ctor_get(v_m_829_, 0);
v_buckets_833_ = lean_ctor_get(v_m_829_, 1);
v___x_834_ = lean_array_get_size(v_buckets_833_);
v___x_835_ = lean_uint64_of_nat(v_a_830_);
v___x_836_ = 32ULL;
v___x_837_ = lean_uint64_shift_right(v___x_835_, v___x_836_);
v_fold_838_ = lean_uint64_xor(v___x_835_, v___x_837_);
v___x_839_ = 16ULL;
v___x_840_ = lean_uint64_shift_right(v_fold_838_, v___x_839_);
v___x_841_ = lean_uint64_xor(v_fold_838_, v___x_840_);
v___x_842_ = lean_uint64_to_usize(v___x_841_);
v___x_843_ = lean_usize_of_nat(v___x_834_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_sub(v___x_843_, v___x_844_);
v___x_846_ = lean_usize_land(v___x_842_, v___x_845_);
v_bkt_847_ = lean_array_uget_borrowed(v_buckets_833_, v___x_846_);
v___x_848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_830_, v_bkt_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_869_; 
lean_inc_ref(v_buckets_833_);
lean_inc(v_size_832_);
v_isSharedCheck_869_ = !lean_is_exclusive(v_m_829_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; lean_object* v_unused_871_; 
v_unused_870_ = lean_ctor_get(v_m_829_, 1);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_m_829_, 0);
lean_dec(v_unused_871_);
v___x_850_ = v_m_829_;
v_isShared_851_ = v_isSharedCheck_869_;
goto v_resetjp_849_;
}
else
{
lean_dec(v_m_829_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_869_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v_size_x27_853_; lean_object* v___x_854_; lean_object* v_buckets_x27_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_852_ = lean_unsigned_to_nat(1u);
v_size_x27_853_ = lean_nat_add(v_size_832_, v___x_852_);
lean_dec(v_size_832_);
lean_inc(v_bkt_847_);
v___x_854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_854_, 0, v_a_830_);
lean_ctor_set(v___x_854_, 1, v_b_831_);
lean_ctor_set(v___x_854_, 2, v_bkt_847_);
v_buckets_x27_855_ = lean_array_uset(v_buckets_833_, v___x_846_, v___x_854_);
v___x_856_ = lean_unsigned_to_nat(4u);
v___x_857_ = lean_nat_mul(v_size_x27_853_, v___x_856_);
v___x_858_ = lean_unsigned_to_nat(3u);
v___x_859_ = lean_nat_div(v___x_857_, v___x_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_array_get_size(v_buckets_x27_855_);
v___x_861_ = lean_nat_dec_le(v___x_859_, v___x_860_);
lean_dec(v___x_859_);
if (v___x_861_ == 0)
{
lean_object* v_val_862_; lean_object* v___x_864_; 
v_val_862_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_855_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_val_862_);
lean_ctor_set(v___x_850_, 0, v_size_x27_853_);
v___x_864_ = v___x_850_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_size_x27_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_val_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_867_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_buckets_x27_855_);
lean_ctor_set(v___x_850_, 0, v_size_x27_853_);
v___x_867_ = v___x_850_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_size_x27_853_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_buckets_x27_855_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_dec(v_b_831_);
lean_dec(v_a_830_);
return v_m_829_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_872_, lean_object* v_as_x27_873_, lean_object* v_b_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
if (lean_obj_tag(v_as_x27_873_) == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v___x_872_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_b_874_);
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; lean_object* v___x_887_; 
v_head_885_ = lean_ctor_get(v_as_x27_873_, 0);
v_tail_886_ = lean_ctor_get(v_as_x27_873_, 1);
lean_inc(v_head_885_);
v___x_887_ = l_Lean_MVarId_getType(v_head_885_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; uint8_t v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
lean_inc_ref(v___x_872_);
v___x_889_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_872_, v_a_888_);
lean_dec(v_a_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_inc(v_head_885_);
v___x_890_ = lean_array_push(v_b_874_, v_head_885_);
v_as_x27_873_ = v_tail_886_;
v_b_874_ = v___x_890_;
goto _start;
}
else
{
lean_object* v___x_892_; lean_object* v_invariants_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_specBackwardRuleCache_898_; lean_object* v_splitBackwardRuleCache_899_; lean_object* v_latticeBackwardRuleCache_900_; lean_object* v_frameBackwardRuleCache_901_; lean_object* v_frameDB_902_; lean_object* v_invariants_903_; lean_object* v_vcs_904_; lean_object* v_simpState_905_; lean_object* v_fuel_906_; lean_object* v_inlineHandledInvariants_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_961_; 
v___x_892_ = lean_st_ref_get(v___y_876_);
v_invariants_893_ = lean_ctor_get(v___x_892_, 5);
lean_inc_ref(v_invariants_893_);
lean_dec(v___x_892_);
v___x_894_ = lean_array_get_size(v_invariants_893_);
lean_dec_ref(v_invariants_893_);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_add(v___x_894_, v___x_895_);
v___x_897_ = lean_st_ref_take(v___y_876_);
v_specBackwardRuleCache_898_ = lean_ctor_get(v___x_897_, 0);
v_splitBackwardRuleCache_899_ = lean_ctor_get(v___x_897_, 1);
v_latticeBackwardRuleCache_900_ = lean_ctor_get(v___x_897_, 2);
v_frameBackwardRuleCache_901_ = lean_ctor_get(v___x_897_, 3);
v_frameDB_902_ = lean_ctor_get(v___x_897_, 4);
v_invariants_903_ = lean_ctor_get(v___x_897_, 5);
v_vcs_904_ = lean_ctor_get(v___x_897_, 6);
v_simpState_905_ = lean_ctor_get(v___x_897_, 7);
v_fuel_906_ = lean_ctor_get(v___x_897_, 8);
v_inlineHandledInvariants_907_ = lean_ctor_get(v___x_897_, 9);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_961_ == 0)
{
v___x_909_ = v___x_897_;
v_isShared_910_ = v_isSharedCheck_961_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_inlineHandledInvariants_907_);
lean_inc(v_fuel_906_);
lean_inc(v_simpState_905_);
lean_inc(v_vcs_904_);
lean_inc(v_invariants_903_);
lean_inc(v_frameDB_902_);
lean_inc(v_frameBackwardRuleCache_901_);
lean_inc(v_latticeBackwardRuleCache_900_);
lean_inc(v_splitBackwardRuleCache_899_);
lean_inc(v_specBackwardRuleCache_898_);
lean_dec(v___x_897_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_961_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_inc(v_head_885_);
v___x_911_ = lean_array_push(v_invariants_903_, v_head_885_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 5, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_specBackwardRuleCache_898_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_splitBackwardRuleCache_899_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_latticeBackwardRuleCache_900_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_frameBackwardRuleCache_901_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_frameDB_902_);
lean_ctor_set(v_reuseFailAlloc_960_, 5, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_960_, 6, v_vcs_904_);
lean_ctor_set(v_reuseFailAlloc_960_, 7, v_simpState_905_);
lean_ctor_set(v_reuseFailAlloc_960_, 8, v_fuel_906_);
lean_ctor_set(v_reuseFailAlloc_960_, 9, v_inlineHandledInvariants_907_);
v___x_913_ = v_reuseFailAlloc_960_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v_invariantAlts_915_; lean_object* v___x_916_; 
v___x_914_ = lean_st_ref_put(v___y_876_, v___x_913_);
v_invariantAlts_915_ = lean_ctor_get(v___y_875_, 3);
lean_inc(v_head_885_);
v___x_916_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_915_, v___x_896_, v_head_885_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; uint8_t v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_unbox(v_a_917_);
lean_dec(v_a_917_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; lean_object* v___x_920_; 
lean_dec(v___x_896_);
v___x_919_ = 2;
lean_inc(v_head_885_);
v___x_920_ = l_Lean_MVarId_setKind___redArg(v_head_885_, v___x_919_, v___y_880_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_dec_ref_known(v___x_920_, 1);
v_as_x27_873_ = v_tail_886_;
goto _start;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_b_874_);
lean_dec_ref(v___x_872_);
v_a_922_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_920_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; lean_object* v_specBackwardRuleCache_931_; lean_object* v_splitBackwardRuleCache_932_; lean_object* v_latticeBackwardRuleCache_933_; lean_object* v_frameBackwardRuleCache_934_; lean_object* v_frameDB_935_; lean_object* v_invariants_936_; lean_object* v_vcs_937_; lean_object* v_simpState_938_; lean_object* v_fuel_939_; lean_object* v_inlineHandledInvariants_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v___x_930_ = lean_st_ref_take(v___y_876_);
v_specBackwardRuleCache_931_ = lean_ctor_get(v___x_930_, 0);
v_splitBackwardRuleCache_932_ = lean_ctor_get(v___x_930_, 1);
v_latticeBackwardRuleCache_933_ = lean_ctor_get(v___x_930_, 2);
v_frameBackwardRuleCache_934_ = lean_ctor_get(v___x_930_, 3);
v_frameDB_935_ = lean_ctor_get(v___x_930_, 4);
v_invariants_936_ = lean_ctor_get(v___x_930_, 5);
v_vcs_937_ = lean_ctor_get(v___x_930_, 6);
v_simpState_938_ = lean_ctor_get(v___x_930_, 7);
v_fuel_939_ = lean_ctor_get(v___x_930_, 8);
v_inlineHandledInvariants_940_ = lean_ctor_get(v___x_930_, 9);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v___x_930_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_inlineHandledInvariants_940_);
lean_inc(v_fuel_939_);
lean_inc(v_simpState_938_);
lean_inc(v_vcs_937_);
lean_inc(v_invariants_936_);
lean_inc(v_frameDB_935_);
lean_inc(v_frameBackwardRuleCache_934_);
lean_inc(v_latticeBackwardRuleCache_933_);
lean_inc(v_splitBackwardRuleCache_932_);
lean_inc(v_specBackwardRuleCache_931_);
lean_dec(v___x_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = lean_box(0);
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_940_, v___x_896_, v___x_944_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 9, v___x_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_specBackwardRuleCache_931_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_splitBackwardRuleCache_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_latticeBackwardRuleCache_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_frameBackwardRuleCache_934_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_frameDB_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_invariants_936_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_vcs_937_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_simpState_938_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_fuel_939_);
lean_ctor_set(v_reuseFailAlloc_950_, 9, v___x_945_);
v___x_947_ = v_reuseFailAlloc_950_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_st_ref_put(v___y_876_, v___x_947_);
v_as_x27_873_ = v_tail_886_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v___x_896_);
lean_dec_ref(v_b_874_);
lean_dec_ref(v___x_872_);
v_a_952_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_916_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_916_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec_ref(v_b_874_);
lean_dec_ref(v___x_872_);
v_a_962_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_887_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_887_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_970_, lean_object* v_as_x27_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_970_, v_as_x27_971_, v_b_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v_as_x27_971_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; lean_object* v_env_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = lean_st_ref_get(v_a_996_);
v_env_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc_ref(v_env_999_);
lean_dec(v___x_998_);
v___x_1000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1001_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_999_, v_subgoals_985_, v___x_1000_, v_a_986_, v_a_987_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_subgoals_1002_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1016_, lean_object* v_m_1017_, lean_object* v_a_1018_, lean_object* v_b_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1017_, v_a_1018_, v_b_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1021_, lean_object* v_as_1022_, lean_object* v_as_x27_1023_, lean_object* v_b_1024_, lean_object* v_a_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1021_, v_as_x27_1023_, v_b_1024_, v___y_1026_, v___y_1027_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1039_ = _args[0];
lean_object* v_as_1040_ = _args[1];
lean_object* v_as_x27_1041_ = _args[2];
lean_object* v_b_1042_ = _args[3];
lean_object* v_a_1043_ = _args[4];
lean_object* v___y_1044_ = _args[5];
lean_object* v___y_1045_ = _args[6];
lean_object* v___y_1046_ = _args[7];
lean_object* v___y_1047_ = _args[8];
lean_object* v___y_1048_ = _args[9];
lean_object* v___y_1049_ = _args[10];
lean_object* v___y_1050_ = _args[11];
lean_object* v___y_1051_ = _args[12];
lean_object* v___y_1052_ = _args[13];
lean_object* v___y_1053_ = _args[14];
lean_object* v___y_1054_ = _args[15];
lean_object* v___y_1055_ = _args[16];
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(v___x_1039_, v_as_1040_, v_as_x27_1041_, v_b_1042_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v_as_x27_1041_);
lean_dec(v_as_1040_);
return v_res_1056_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1057_, lean_object* v_a_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1061_, lean_object* v_a_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1061_, v_a_1062_, v_x_1063_);
lean_dec(v_x_1063_);
lean_dec(v_a_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1066_, lean_object* v_data_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1069_, lean_object* v_i_1070_, lean_object* v_source_1071_, lean_object* v_target_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1070_, v_source_1071_, v_target_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1075_, v_x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_toGoalState_1091_; lean_object* v_mvarId_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1188_; 
v_toGoalState_1091_ = lean_ctor_get(v_goal_1078_, 0);
v_mvarId_1092_ = lean_ctor_get(v_goal_1078_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_goal_1078_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1094_ = v_goal_1078_;
v_isShared_1095_ = v_isSharedCheck_1188_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_mvarId_1092_);
lean_inc(v_toGoalState_1091_);
lean_dec(v_goal_1078_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1188_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1092_, v_a_1079_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_a_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_toGoalState_1091_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_a_1097_);
v___x_1099_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v___x_1099_, v_a_1079_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1170_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1170_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1170_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_toGoalState_1105_; uint8_t v_inconsistent_1106_; 
v_toGoalState_1105_ = lean_ctor_get(v_a_1101_, 0);
lean_inc_ref(v_toGoalState_1105_);
v_inconsistent_1106_ = lean_ctor_get_uint8(v_toGoalState_1105_, sizeof(void*)*18);
if (v_inconsistent_1106_ == 0)
{
lean_object* v_mvarId_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1164_; 
lean_del_object(v___x_1103_);
v_mvarId_1107_ = lean_ctor_get(v_a_1101_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_a_1101_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v_a_1101_, 0);
lean_dec(v_unused_1165_);
v___x_1109_ = v_a_1101_;
v_isShared_1110_ = v_isSharedCheck_1164_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_mvarId_1107_);
lean_dec(v_a_1101_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1164_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_mvarId_1107_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1155_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1155_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1155_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
if (lean_obj_tag(v_a_1112_) == 1)
{
lean_object* v_val_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; 
lean_del_object(v___x_1114_);
v_val_1116_ = lean_ctor_get(v_a_1112_, 0);
lean_inc_n(v_val_1116_, 2);
lean_dec_ref_known(v_a_1112_, 1);
v___x_1117_ = 2;
v___x_1118_ = l_Lean_MVarId_setKind___redArg(v_val_1116_, v___x_1117_, v_a_1087_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1149_; 
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1150_);
v___x_1120_ = v___x_1118_;
v_isShared_1121_ = v_isSharedCheck_1149_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1149_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v_specBackwardRuleCache_1123_; lean_object* v_splitBackwardRuleCache_1124_; lean_object* v_latticeBackwardRuleCache_1125_; lean_object* v_frameBackwardRuleCache_1126_; lean_object* v_frameDB_1127_; lean_object* v_invariants_1128_; lean_object* v_vcs_1129_; lean_object* v_simpState_1130_; lean_object* v_fuel_1131_; lean_object* v_inlineHandledInvariants_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1148_; 
v___x_1122_ = lean_st_ref_take(v_a_1080_);
v_specBackwardRuleCache_1123_ = lean_ctor_get(v___x_1122_, 0);
v_splitBackwardRuleCache_1124_ = lean_ctor_get(v___x_1122_, 1);
v_latticeBackwardRuleCache_1125_ = lean_ctor_get(v___x_1122_, 2);
v_frameBackwardRuleCache_1126_ = lean_ctor_get(v___x_1122_, 3);
v_frameDB_1127_ = lean_ctor_get(v___x_1122_, 4);
v_invariants_1128_ = lean_ctor_get(v___x_1122_, 5);
v_vcs_1129_ = lean_ctor_get(v___x_1122_, 6);
v_simpState_1130_ = lean_ctor_get(v___x_1122_, 7);
v_fuel_1131_ = lean_ctor_get(v___x_1122_, 8);
v_inlineHandledInvariants_1132_ = lean_ctor_get(v___x_1122_, 9);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1134_ = v___x_1122_;
v_isShared_1135_ = v_isSharedCheck_1148_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_inlineHandledInvariants_1132_);
lean_inc(v_fuel_1131_);
lean_inc(v_simpState_1130_);
lean_inc(v_vcs_1129_);
lean_inc(v_invariants_1128_);
lean_inc(v_frameDB_1127_);
lean_inc(v_frameBackwardRuleCache_1126_);
lean_inc(v_latticeBackwardRuleCache_1125_);
lean_inc(v_splitBackwardRuleCache_1124_);
lean_inc(v_specBackwardRuleCache_1123_);
lean_dec(v___x_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1148_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_box(0);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 1, v_val_1116_);
v___x_1138_ = v___x_1109_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_toGoalState_1105_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_val_1116_);
v___x_1138_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_array_push(v_vcs_1129_, v___x_1138_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 6, v___x_1139_);
v___x_1141_ = v___x_1134_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_specBackwardRuleCache_1123_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_splitBackwardRuleCache_1124_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_latticeBackwardRuleCache_1125_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_frameBackwardRuleCache_1126_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v_frameDB_1127_);
lean_ctor_set(v_reuseFailAlloc_1146_, 5, v_invariants_1128_);
lean_ctor_set(v_reuseFailAlloc_1146_, 6, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1146_, 7, v_simpState_1130_);
lean_ctor_set(v_reuseFailAlloc_1146_, 8, v_fuel_1131_);
lean_ctor_set(v_reuseFailAlloc_1146_, 9, v_inlineHandledInvariants_1132_);
v___x_1141_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_st_ref_put(v_a_1080_, v___x_1141_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1136_);
v___x_1144_ = v___x_1120_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1136_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1116_);
lean_del_object(v___x_1109_);
lean_dec_ref(v_toGoalState_1105_);
return v___x_1118_;
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_dec(v_a_1112_);
lean_del_object(v___x_1109_);
lean_dec_ref(v_toGoalState_1105_);
v___x_1151_ = lean_box(0);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1151_);
v___x_1153_ = v___x_1114_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_del_object(v___x_1109_);
lean_dec_ref(v_toGoalState_1105_);
v_a_1156_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1111_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1111_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec_ref(v_toGoalState_1105_);
lean_dec(v_a_1101_);
v___x_1166_ = lean_box(0);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1166_);
v___x_1168_ = v___x_1103_;
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
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1100_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1100_);
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
lean_del_object(v___x_1094_);
lean_dec_ref(v_toGoalState_1091_);
v_a_1180_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1096_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1096_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object* v_mvarId_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v_mctx_1207_; lean_object* v_eAssignment_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = lean_st_ref_get(v___y_1204_);
v_mctx_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref(v_mctx_1207_);
lean_dec(v___x_1206_);
v_eAssignment_1208_ = lean_ctor_get(v_mctx_1207_, 8);
lean_inc_ref(v_eAssignment_1208_);
lean_dec_ref(v_mctx_1207_);
v___x_1209_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1208_, v_mvarId_1203_);
lean_dec_ref(v_eAssignment_1208_);
v___x_1210_ = lean_box(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object* v_mvarId_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec(v_mvarId_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v___x_1216_, lean_object* v_scope_1217_, size_t v_sz_1218_, size_t v_i_1219_, lean_object* v_bs_1220_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_lt(v_i_1219_, v_sz_1218_);
if (v___x_1221_ == 0)
{
lean_dec_ref(v_scope_1217_);
lean_dec_ref(v___x_1216_);
return v_bs_1220_;
}
else
{
lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_bs_x27_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v_v_1222_ = lean_array_uget(v_bs_1220_, v_i_1219_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v_bs_x27_1224_ = lean_array_uset(v_bs_1220_, v_i_1219_, v___x_1223_);
lean_inc_ref(v___x_1216_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1216_);
lean_ctor_set(v___x_1225_, 1, v_v_1222_);
lean_inc_ref(v_scope_1217_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_scope_1217_);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_add(v_i_1219_, v___x_1227_);
v___x_1229_ = lean_array_uset(v_bs_x27_1224_, v_i_1219_, v___x_1226_);
v_i_1219_ = v___x_1228_;
v_bs_1220_ = v___x_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v___x_1231_, lean_object* v_scope_1232_, lean_object* v_sz_1233_, lean_object* v_i_1234_, lean_object* v_bs_1235_){
_start:
{
size_t v_sz_boxed_1236_; size_t v_i_boxed_1237_; lean_object* v_res_1238_; 
v_sz_boxed_1236_ = lean_unbox_usize(v_sz_1233_);
lean_dec(v_sz_1233_);
v_i_boxed_1237_ = lean_unbox_usize(v_i_1234_);
lean_dec(v_i_1234_);
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v___x_1231_, v_scope_1232_, v_sz_boxed_1236_, v_i_boxed_1237_, v_bs_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_a_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1252_ = lean_array_get_size(v_a_1239_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_sub(v___x_1252_, v___x_1253_);
v___x_1255_ = lean_nat_dec_lt(v___x_1254_, v___x_1252_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec(v___x_1254_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_a_1239_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v_goal_1258_; lean_object* v_scope_1259_; lean_object* v_mvarId_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1257_ = lean_array_fget_borrowed(v_a_1239_, v___x_1254_);
lean_dec(v___x_1254_);
v_goal_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_goal_1258_);
v_scope_1259_ = lean_ctor_get(v___x_1257_, 1);
lean_inc_ref(v_scope_1259_);
v_mvarId_1260_ = lean_ctor_get(v_goal_1258_, 1);
v___x_1261_ = lean_array_pop(v_a_1239_);
v___x_1262_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1260_, v___y_1248_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; uint8_t v___x_1264_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_unbox(v_a_1263_);
lean_dec(v_a_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1258_, v___y_1240_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v_toGoalState_1267_; uint8_t v_inconsistent_1268_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v_toGoalState_1267_ = lean_ctor_get(v_a_1266_, 0);
v_inconsistent_1268_ = lean_ctor_get_uint8(v_toGoalState_1267_, sizeof(void*)*18);
if (v_inconsistent_1268_ == 0)
{
lean_object* v_mvarId_1269_; lean_object* v___x_1270_; 
v_mvarId_1269_ = lean_ctor_get(v_a_1266_, 1);
lean_inc(v_mvarId_1269_);
v___x_1270_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1259_, v_mvarId_1269_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
if (lean_obj_tag(v_a_1271_) == 0)
{
lean_object* v_scope_1272_; lean_object* v_subgoals_1273_; lean_object* v___x_1274_; 
lean_inc_ref(v_toGoalState_1267_);
lean_dec(v_a_1266_);
v_scope_1272_ = lean_ctor_get(v_a_1271_, 0);
lean_inc_ref(v_scope_1272_);
v_subgoals_1273_ = lean_ctor_get(v_a_1271_, 1);
lean_inc(v_subgoals_1273_);
lean_dec_ref_known(v_a_1271_, 2);
v___x_1274_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1273_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v_subgoals_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = l_Array_reverse___redArg(v_a_1275_);
v_sz_1277_ = lean_array_size(v___x_1276_);
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_toGoalState_1267_, v_scope_1272_, v_sz_1277_, v___x_1278_, v___x_1276_);
v___x_1280_ = l_Array_append___redArg(v___x_1261_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v_a_1239_ = v___x_1280_;
goto _start;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_scope_1272_);
lean_dec_ref(v_toGoalState_1267_);
lean_dec_ref(v___x_1261_);
v_a_1282_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1274_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1274_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v___x_1290_; 
lean_dec_ref_known(v_a_1271_, 1);
v___x_1290_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1266_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_dec_ref_known(v___x_1290_, 1);
v_a_1239_ = v___x_1261_;
goto _start;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v___x_1261_);
v_a_1292_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1290_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_a_1266_);
lean_dec_ref(v___x_1261_);
v_a_1300_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1270_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1270_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_dec(v_a_1266_);
lean_dec_ref(v_scope_1259_);
v_a_1239_ = v___x_1261_;
goto _start;
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v___x_1261_);
lean_dec_ref(v_scope_1259_);
v_a_1309_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1265_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1265_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1259_);
lean_dec_ref(v_goal_1258_);
v_a_1239_ = v___x_1261_;
goto _start;
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v___x_1261_);
lean_dec_ref(v_scope_1259_);
lean_dec_ref(v_goal_1258_);
v_a_1318_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1262_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1262_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_a_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1340_, lean_object* v_goal_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_toGoalState_1354_; lean_object* v_mvarId_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1394_; 
v_toGoalState_1354_ = lean_ctor_get(v_goal_1341_, 0);
v_mvarId_1355_ = lean_ctor_get(v_goal_1341_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_goal_1341_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1357_ = v_goal_1341_;
v_isShared_1358_ = v_isSharedCheck_1394_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_mvarId_1355_);
lean_inc(v_toGoalState_1354_);
lean_dec(v_goal_1341_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1394_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1355_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 1, v_a_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_toGoalState_1354_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_a_1360_);
v___x_1362_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v_scope_1340_);
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_mk_empty_array_with_capacity(v___x_1364_);
v___x_1366_ = lean_array_push(v___x_1365_, v___x_1363_);
v___x_1367_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v___x_1366_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1376_);
v___x_1369_ = v___x_1367_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_box(0);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_a_1377_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1367_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1367_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_del_object(v___x_1357_);
lean_dec_ref(v_toGoalState_1354_);
lean_dec_ref(v_scope_1340_);
v_a_1386_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1359_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1359_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1395_, lean_object* v_goal_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1395_, v_goal_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v_mvarId_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1410_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v_mvarId_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_mvarId_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v_mvarId_1424_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_inst_1438_, lean_object* v_a_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_inst_1453_, lean_object* v_a_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_inst_1453_, v_a_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_config_1479_; lean_object* v_sharedExprs_1480_; uint8_t v_verbose_1481_; uint8_t v_enforceUnfoldReducible_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_config_1479_ = lean_ctor_get(v___y_1472_, 1);
v_sharedExprs_1480_ = lean_ctor_get(v___y_1472_, 0);
v_verbose_1481_ = lean_ctor_get_uint8(v_config_1479_, 0);
v_enforceUnfoldReducible_1482_ = lean_ctor_get_uint8(v_config_1479_, 1);
v___x_1483_ = 0;
v___x_1484_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_1484_, 0, v_verbose_1481_);
lean_ctor_set_uint8(v___x_1484_, 1, v_enforceUnfoldReducible_1482_);
lean_ctor_set_uint8(v___x_1484_, 2, v___x_1483_);
lean_inc_ref(v_sharedExprs_1480_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_sharedExprs_1480_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
v___x_1486_ = lean_apply_10(v_x_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___x_1485_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, lean_box(0));
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_1512_, v_x_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_1525_, lean_object* v_scope_1526_, lean_object* v_goal_1527_, lean_object* v_ctx_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_st_mk_ref(v_initState_1525_);
v___x_1540_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1526_, v_goal_1527_, v_ctx_1528_, v___x_1539_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1550_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1550_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1550_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1545_ = lean_st_ref_get(v___x_1539_);
lean_dec(v___x_1539_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_a_1541_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1546_);
v___x_1548_ = v___x_1543_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v___x_1539_);
v_a_1551_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1540_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1540_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_1559_, lean_object* v_scope_1560_, lean_object* v_goal_1561_, lean_object* v_ctx_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_1559_, v_scope_1560_, v_goal_1561_, v_ctx_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v_ctx_1562_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_mctx_1578_; lean_object* v_eAssignment_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1577_ = lean_st_ref_get(v___y_1575_);
v_mctx_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_mctx_1578_);
lean_dec(v___x_1577_);
v_eAssignment_1579_ = lean_ctor_get(v_mctx_1578_, 8);
lean_inc_ref(v_eAssignment_1579_);
lean_dec_ref(v_mctx_1578_);
v___x_1580_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1579_, v_mvarId_1574_);
lean_dec_ref(v_eAssignment_1579_);
v___x_1581_ = lean_box(v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec(v_mvarId_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_1587_, size_t v_i_1588_, size_t v_stop_1589_, lean_object* v_b_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_a_1602_; uint8_t v___x_1606_; 
v___x_1606_ = lean_usize_dec_eq(v_i_1588_, v_stop_1589_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v_mvarId_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_array_uget_borrowed(v_as_1587_, v_i_1588_);
v_mvarId_1608_ = lean_ctor_get(v___x_1607_, 1);
v___x_1609_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1608_, v___y_1597_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; uint8_t v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = lean_unbox(v_a_1610_);
lean_dec(v_a_1610_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_inc(v___x_1607_);
v___x_1612_ = lean_array_push(v_b_1590_, v___x_1607_);
v_a_1602_ = v___x_1612_;
goto v___jp_1601_;
}
else
{
v_a_1602_ = v_b_1590_;
goto v___jp_1601_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_b_1590_);
v_a_1613_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1609_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1609_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_b_1590_);
return v___x_1621_;
}
v___jp_1601_:
{
size_t v___x_1603_; size_t v___x_1604_; 
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_add(v_i_1588_, v___x_1603_);
v_i_1588_ = v___x_1604_;
v_b_1590_ = v_a_1602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_1622_, lean_object* v_i_1623_, lean_object* v_stop_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
size_t v_i_boxed_1636_; size_t v_stop_boxed_1637_; lean_object* v_res_1638_; 
v_i_boxed_1636_ = lean_unbox_usize(v_i_1623_);
lean_dec(v_i_1623_);
v_stop_boxed_1637_ = lean_unbox_usize(v_stop_1624_);
lean_dec(v_stop_1624_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_1622_, v_i_boxed_1636_, v_stop_boxed_1637_, v_b_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v_as_1622_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_1640_, size_t v_i_1641_, lean_object* v_bs_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_usize_dec_lt(v_i_1641_, v_sz_1640_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_bs_1642_);
return v___x_1649_;
}
else
{
lean_object* v_v_1650_; lean_object* v_mvarId_1651_; lean_object* v___x_1652_; lean_object* v_bs_x27_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_v_1650_ = lean_array_uget_borrowed(v_bs_1642_, v_i_1641_);
v_mvarId_1651_ = lean_ctor_get(v_v_1650_, 1);
lean_inc_n(v_mvarId_1651_, 2);
v___x_1652_ = lean_unsigned_to_nat(0u);
v_bs_x27_1653_ = lean_array_uset(v_bs_1642_, v_i_1641_, v___x_1652_);
v___x_1654_ = lean_usize_to_nat(v_i_1641_);
v___x_1655_ = l_Lean_MVarId_getTag(v_mvarId_1651_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v___x_1657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_add(v___x_1654_, v___x_1658_);
lean_dec(v___x_1654_);
v___x_1660_ = l_Nat_reprFast(v___x_1659_);
v___x_1661_ = lean_string_append(v___x_1657_, v___x_1660_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = lean_box(0);
v___x_1663_ = l_Lean_Name_str___override(v___x_1662_, v___x_1661_);
v___x_1664_ = l_Lean_Name_eraseMacroScopes(v_a_1656_);
lean_dec(v_a_1656_);
v___x_1665_ = l_Lean_Name_append(v___x_1663_, v___x_1664_);
v___x_1666_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1651_, v___x_1665_, v___y_1644_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; size_t v___x_1668_; size_t v___x_1669_; lean_object* v___x_1670_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = ((size_t)1ULL);
v___x_1669_ = lean_usize_add(v_i_1641_, v___x_1668_);
v___x_1670_ = lean_array_uset(v_bs_x27_1653_, v_i_1641_, v_a_1667_);
v_i_1641_ = v___x_1669_;
v_bs_1642_ = v___x_1670_;
goto _start;
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec_ref(v_bs_x27_1653_);
v_a_1672_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1666_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1666_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v___x_1654_);
lean_dec_ref(v_bs_x27_1653_);
lean_dec(v_mvarId_1651_);
v_a_1680_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1655_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1655_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_1688_, lean_object* v_i_1689_, lean_object* v_bs_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
size_t v_sz_boxed_1696_; size_t v_i_boxed_1697_; lean_object* v_res_1698_; 
v_sz_boxed_1696_ = lean_unbox_usize(v_sz_1688_);
lean_dec(v_sz_1688_);
v_i_boxed_1697_ = lean_unbox_usize(v_i_1689_);
lean_dec(v_i_1689_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_1696_, v_i_boxed_1697_, v_bs_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_bs_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_bs_1702_);
return v___x_1706_;
}
else
{
lean_object* v_v_1707_; lean_object* v___x_1708_; lean_object* v_bs_x27_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_v_1707_ = lean_array_uget(v_bs_1702_, v_i_1701_);
v___x_1708_ = lean_unsigned_to_nat(0u);
v_bs_x27_1709_ = lean_array_uset(v_bs_1702_, v_i_1701_, v___x_1708_);
v___x_1710_ = lean_usize_to_nat(v_i_1701_);
v___x_1711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_1712_ = lean_unsigned_to_nat(1u);
v___x_1713_ = lean_nat_add(v___x_1710_, v___x_1712_);
lean_dec(v___x_1710_);
v___x_1714_ = l_Nat_reprFast(v___x_1713_);
v___x_1715_ = lean_string_append(v___x_1711_, v___x_1714_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = lean_box(0);
v___x_1717_ = l_Lean_Name_str___override(v___x_1716_, v___x_1715_);
v___x_1718_ = l_Lean_MVarId_setTag___redArg(v_v_1707_, v___x_1717_, v___y_1703_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1701_, v___x_1720_);
v___x_1722_ = lean_array_uset(v_bs_x27_1709_, v_i_1701_, v_a_1719_);
v_i_1701_ = v___x_1721_;
v_bs_1702_ = v___x_1722_;
goto _start;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_bs_x27_1709_);
v_a_1724_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1718_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1718_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1734_, v___y_1735_);
lean_dec(v___y_1735_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_1740_, size_t v_i_1741_, size_t v_stop_1742_, lean_object* v_b_1743_){
_start:
{
lean_object* v___y_1745_; uint8_t v___x_1749_; 
v___x_1749_ = lean_usize_dec_eq(v_i_1741_, v_stop_1742_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; uint8_t v_retired_1751_; 
v___x_1750_ = lean_array_uget_borrowed(v_as_1740_, v_i_1741_);
v_retired_1751_ = lean_ctor_get_uint8(v___x_1750_, sizeof(void*)*4);
if (v_retired_1751_ == 0)
{
lean_object* v_frameStx_1752_; lean_object* v___x_1753_; 
v_frameStx_1752_ = lean_ctor_get(v___x_1750_, 2);
lean_inc(v_frameStx_1752_);
v___x_1753_ = lean_array_push(v_b_1743_, v_frameStx_1752_);
v___y_1745_ = v___x_1753_;
goto v___jp_1744_;
}
else
{
v___y_1745_ = v_b_1743_;
goto v___jp_1744_;
}
}
else
{
return v_b_1743_;
}
v___jp_1744_:
{
size_t v___x_1746_; size_t v___x_1747_; 
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1741_, v___x_1746_);
v_i_1741_ = v___x_1747_;
v_b_1743_ = v___y_1745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_1754_, lean_object* v_i_1755_, lean_object* v_stop_1756_, lean_object* v_b_1757_){
_start:
{
size_t v_i_boxed_1758_; size_t v_stop_boxed_1759_; lean_object* v_res_1760_; 
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_stop_boxed_1759_ = lean_unbox_usize(v_stop_1756_);
lean_dec(v_stop_1756_);
v_res_1760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1754_, v_i_boxed_1758_, v_stop_boxed_1759_, v_b_1757_);
lean_dec_ref(v_as_1754_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_1763_, lean_object* v_start_1764_, lean_object* v_stop_1765_){
_start:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0));
v___x_1767_ = lean_nat_dec_lt(v_start_1764_, v_stop_1765_);
if (v___x_1767_ == 0)
{
return v___x_1766_;
}
else
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_array_get_size(v_as_1763_);
v___x_1769_ = lean_nat_dec_le(v_stop_1765_, v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_lt(v_start_1764_, v___x_1768_);
if (v___x_1770_ == 0)
{
return v___x_1766_;
}
else
{
size_t v___x_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_usize_of_nat(v_start_1764_);
v___x_1772_ = lean_usize_of_nat(v___x_1768_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1763_, v___x_1771_, v___x_1772_, v___x_1766_);
return v___x_1773_;
}
}
else
{
size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_usize_of_nat(v_start_1764_);
v___x_1775_ = lean_usize_of_nat(v_stop_1765_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1763_, v___x_1774_, v___x_1775_, v___x_1766_);
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_1777_, lean_object* v_start_1778_, lean_object* v_stop_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_1777_, v_start_1778_, v_stop_1779_);
lean_dec(v_stop_1779_);
lean_dec(v_start_1778_);
lean_dec_ref(v_as_1777_);
return v_res_1780_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_unsigned_to_nat(16u);
v___x_1783_ = lean_mk_array(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1787_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1790_);
lean_ctor_set(v___x_1792_, 2, v___x_1790_);
lean_ctor_set(v___x_1792_, 3, v___x_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_1793_, lean_object* v_ctx_1794_, lean_object* v_scope_1795_, lean_object* v_stepLimit_x3f_1796_, lean_object* v_frameDB_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v_a_1813_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___y_1823_; 
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_1820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1821_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1796_) == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_box(1);
v___y_1823_ = v___x_1875_;
goto v___jp_1822_;
}
else
{
lean_object* v_val_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_val_1876_ = lean_ctor_get(v_stepLimit_x3f_1796_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_stepLimit_x3f_1796_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v_stepLimit_x3f_1796_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_val_1876_);
lean_dec(v_stepLimit_x3f_1796_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 0);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_val_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
v___y_1823_ = v___x_1881_;
goto v___jp_1822_;
}
}
}
v___jp_1809_:
{
lean_object* v_entries_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_entries_1814_ = lean_ctor_get(v___y_1811_, 1);
lean_inc_ref(v_entries_1814_);
lean_dec_ref(v___y_1811_);
v___x_1815_ = lean_array_get_size(v_entries_1814_);
v___x_1816_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_1814_, v___x_1808_, v___x_1815_);
lean_dec_ref(v_entries_1814_);
v___x_1817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1817_, 0, v___y_1810_);
lean_ctor_set(v___x_1817_, 1, v_a_1813_);
lean_ctor_set(v___x_1817_, 2, v___y_1812_);
lean_ctor_set(v___x_1817_, 3, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
v___jp_1822_:
{
lean_object* v_initState_1824_; lean_object* v___f_1825_; lean_object* v___x_1826_; 
v_initState_1824_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_initState_1824_, 0, v___x_1819_);
lean_ctor_set(v_initState_1824_, 1, v___x_1819_);
lean_ctor_set(v_initState_1824_, 2, v___x_1819_);
lean_ctor_set(v_initState_1824_, 3, v___x_1819_);
lean_ctor_set(v_initState_1824_, 4, v_frameDB_1797_);
lean_ctor_set(v_initState_1824_, 5, v___x_1820_);
lean_ctor_set(v_initState_1824_, 6, v___x_1820_);
lean_ctor_set(v_initState_1824_, 7, v___x_1821_);
lean_ctor_set(v_initState_1824_, 8, v___y_1823_);
lean_ctor_set(v_initState_1824_, 9, v___x_1819_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1825_, 0, v_initState_1824_);
lean_closure_set(v___f_1825_, 1, v_scope_1795_);
lean_closure_set(v___f_1825_, 2, v_goal_1793_);
lean_closure_set(v___f_1825_, 3, v_ctx_1794_);
v___x_1826_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_1825_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v_snd_1828_; lean_object* v_frameDB_1829_; lean_object* v_invariants_1830_; lean_object* v_vcs_1831_; lean_object* v_inlineHandledInvariants_1832_; size_t v_sz_1833_; size_t v___x_1834_; lean_object* v___x_1835_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v_snd_1828_ = lean_ctor_get(v_a_1827_, 1);
lean_inc(v_snd_1828_);
lean_dec(v_a_1827_);
v_frameDB_1829_ = lean_ctor_get(v_snd_1828_, 4);
lean_inc_ref(v_frameDB_1829_);
v_invariants_1830_ = lean_ctor_get(v_snd_1828_, 5);
lean_inc_ref_n(v_invariants_1830_, 2);
v_vcs_1831_ = lean_ctor_get(v_snd_1828_, 6);
lean_inc_ref(v_vcs_1831_);
v_inlineHandledInvariants_1832_ = lean_ctor_get(v_snd_1828_, 9);
lean_inc_ref(v_inlineHandledInvariants_1832_);
lean_dec(v_snd_1828_);
v_sz_1833_ = lean_array_size(v_invariants_1830_);
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1833_, v___x_1834_, v_invariants_1830_, v_a_1804_);
if (lean_obj_tag(v___x_1835_) == 0)
{
size_t v_sz_1836_; lean_object* v___x_1837_; 
lean_dec_ref_known(v___x_1835_, 1);
v_sz_1836_ = lean_array_size(v_vcs_1831_);
lean_inc_ref(v_vcs_1831_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1836_, v___x_1834_, v_vcs_1831_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
lean_dec_ref_known(v___x_1837_, 1);
v___x_1838_ = lean_array_get_size(v_vcs_1831_);
v___x_1839_ = lean_nat_dec_lt(v___x_1808_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec_ref(v_vcs_1831_);
v___y_1810_ = v_invariants_1830_;
v___y_1811_ = v_frameDB_1829_;
v___y_1812_ = v_inlineHandledInvariants_1832_;
v_a_1813_ = v___x_1820_;
goto v___jp_1809_;
}
else
{
size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_usize_of_nat(v___x_1838_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1831_, v___x_1834_, v___x_1840_, v___x_1820_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec_ref(v_vcs_1831_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___y_1810_ = v_invariants_1830_;
v___y_1811_ = v_frameDB_1829_;
v___y_1812_ = v_inlineHandledInvariants_1832_;
v_a_1813_ = v_a_1842_;
goto v___jp_1809_;
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v_inlineHandledInvariants_1832_);
lean_dec_ref(v_invariants_1830_);
lean_dec_ref(v_frameDB_1829_);
v_a_1843_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1841_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1841_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v_inlineHandledInvariants_1832_);
lean_dec_ref(v_vcs_1831_);
lean_dec_ref(v_invariants_1830_);
lean_dec_ref(v_frameDB_1829_);
v_a_1851_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1837_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1837_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_inlineHandledInvariants_1832_);
lean_dec_ref(v_vcs_1831_);
lean_dec_ref(v_invariants_1830_);
lean_dec_ref(v_frameDB_1829_);
v_a_1859_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1835_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1835_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1826_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1826_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_1884_, lean_object* v_ctx_1885_, lean_object* v_scope_1886_, lean_object* v_stepLimit_x3f_1887_, lean_object* v_frameDB_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_1884_, v_ctx_1885_, v_scope_1886_, v_stepLimit_x3f_1887_, v_frameDB_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1900_, v___y_1907_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec(v_mvarId_1912_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_1924_, size_t v_sz_1925_, size_t v_i_1926_, lean_object* v_bs_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1925_, v_i_1926_, v_bs_1927_, v___y_1934_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_1939_, lean_object* v_sz_1940_, lean_object* v_i_1941_, lean_object* v_bs_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
size_t v_sz_boxed_1953_; size_t v_i_boxed_1954_; lean_object* v_res_1955_; 
v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1940_);
lean_dec(v_sz_1940_);
v_i_boxed_1954_ = lean_unbox_usize(v_i_1941_);
lean_dec(v_i_1941_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_1939_, v_sz_boxed_1953_, v_i_boxed_1954_, v_bs_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v_as_1939_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_1956_, size_t v_sz_1957_, size_t v_i_1958_, lean_object* v_bs_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1957_, v_i_1958_, v_bs_1959_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_1971_, lean_object* v_sz_1972_, lean_object* v_i_1973_, lean_object* v_bs_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
size_t v_sz_boxed_1985_; size_t v_i_boxed_1986_; lean_object* v_res_1987_; 
v_sz_boxed_1985_ = lean_unbox_usize(v_sz_1972_);
lean_dec(v_sz_1972_);
v_i_boxed_1986_ = lean_unbox_usize(v_i_1973_);
lean_dec(v_i_1973_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_1971_, v_sz_boxed_1985_, v_i_boxed_1986_, v_bs_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v_as_1971_);
return v_res_1987_;
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
