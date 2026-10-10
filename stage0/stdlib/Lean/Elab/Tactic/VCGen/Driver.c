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
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(lean_object* v_mvarId_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mvarId_1_, v___y_2_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object* v_mvarId_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mvarId_9_, v___y_10_);
lean_dec(v___y_10_);
lean_dec(v_mvarId_9_);
return v_res_12_;
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(lean_object* v_mvarId_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mvarId_13_, v___y_17_);
return v___x_21_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_13_ = stack[0].m_obj;
lean_object* v___y_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v___y_18_ = stack[5].m_obj;
lean_object* v___y_19_ = stack[6].m_obj;
lean_object* v_res_22_;
v_res_22_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(v_mvarId_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___boxed(lean_object* v_mvarId_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(v_mvarId_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v_mvarId_23_);
return v_res_31_;
}
}
uint8_t l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(lean_object* v_x_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_32_ = stack[0].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(v_x_32_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed(lean_object* v_x_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(v_x_35_);
lean_dec(v_x_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_x_38_, lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_ks_42_; lean_object* v_vs_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_67_; 
v_ks_42_ = lean_ctor_get(v_x_38_, 0);
v_vs_43_ = lean_ctor_get(v_x_38_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_38_);
if (v_isSharedCheck_67_ == 0)
{
v___x_45_ = v_x_38_;
v_isShared_46_ = v_isSharedCheck_67_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_vs_43_);
lean_inc(v_ks_42_);
lean_dec(v_x_38_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_67_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_array_get_size(v_ks_42_);
v___x_48_ = lean_nat_dec_lt(v_x_39_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
lean_dec(v_x_39_);
v___x_49_ = lean_array_push(v_ks_42_, v_x_40_);
v___x_50_ = lean_array_push(v_vs_43_, v_x_41_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_50_);
lean_ctor_set(v___x_45_, 0, v___x_49_);
v___x_52_ = v___x_45_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
else
{
lean_object* v_k_x27_54_; uint8_t v___x_55_; 
v_k_x27_54_ = lean_array_fget_borrowed(v_ks_42_, v_x_39_);
v___x_55_ = l_Lean_instBEqMVarId_beq(v_x_40_, v_k_x27_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_57_; 
if (v_isShared_46_ == 0)
{
v___x_57_ = v___x_45_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_ks_42_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_vs_43_);
v___x_57_ = v_reuseFailAlloc_61_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_x_39_, v___x_58_);
lean_dec(v_x_39_);
v_x_38_ = v___x_57_;
v_x_39_ = v___x_59_;
goto _start;
}
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_62_ = lean_array_fset(v_ks_42_, v_x_39_, v_x_40_);
v___x_63_ = lean_array_fset(v_vs_43_, v_x_39_, v_x_41_);
lean_dec(v_x_39_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_63_);
lean_ctor_set(v___x_45_, 0, v___x_62_);
v___x_65_ = v___x_45_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_n_68_, lean_object* v_k_69_, lean_object* v_v_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_n_68_, v___x_71_, v_k_69_, v_v_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_73_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object* v_x_74_, size_t v_x_75_, size_t v_x_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_es_79_; size_t v___x_80_; size_t v___x_81_; lean_object* v_j_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_es_79_ = lean_ctor_get(v_x_74_, 0);
v___x_80_ = ((size_t)31ULL);
v___x_81_ = lean_usize_land(v_x_75_, v___x_80_);
v_j_82_ = lean_usize_to_nat(v___x_81_);
v___x_83_ = lean_array_get_size(v_es_79_);
v___x_84_ = lean_nat_dec_lt(v_j_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_dec(v_j_82_);
lean_dec(v_x_78_);
lean_dec(v_x_77_);
return v_x_74_;
}
else
{
lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_123_; 
lean_inc_ref(v_es_79_);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; 
v_unused_124_ = lean_ctor_get(v_x_74_, 0);
lean_dec(v_unused_124_);
v___x_86_ = v_x_74_;
v_isShared_87_ = v_isSharedCheck_123_;
goto v_resetjp_85_;
}
else
{
lean_dec(v_x_74_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_123_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_v_88_; lean_object* v___x_89_; lean_object* v_xs_x27_90_; lean_object* v___y_92_; 
v_v_88_ = lean_array_fget(v_es_79_, v_j_82_);
v___x_89_ = lean_box(0);
v_xs_x27_90_ = lean_array_fset(v_es_79_, v_j_82_, v___x_89_);
switch(lean_obj_tag(v_v_88_))
{
case 0:
{
lean_object* v_key_97_; lean_object* v_val_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_108_; 
v_key_97_ = lean_ctor_get(v_v_88_, 0);
v_val_98_ = lean_ctor_get(v_v_88_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_v_88_);
if (v_isSharedCheck_108_ == 0)
{
v___x_100_ = v_v_88_;
v_isShared_101_ = v_isSharedCheck_108_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_val_98_);
lean_inc(v_key_97_);
lean_dec(v_v_88_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_108_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
uint8_t v___x_102_; 
v___x_102_ = l_Lean_instBEqMVarId_beq(v_x_77_, v_key_97_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_del_object(v___x_100_);
v___x_103_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_97_, v_val_98_, v_x_77_, v_x_78_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___y_92_ = v___x_104_;
goto v___jp_91_;
}
else
{
lean_object* v___x_106_; 
lean_dec(v_val_98_);
lean_dec(v_key_97_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v_x_78_);
lean_ctor_set(v___x_100_, 0, v_x_77_);
v___x_106_ = v___x_100_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_x_77_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_x_78_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
v___y_92_ = v___x_106_;
goto v___jp_91_;
}
}
}
}
case 1:
{
lean_object* v_node_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_121_; 
v_node_109_ = lean_ctor_get(v_v_88_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v_v_88_);
if (v_isSharedCheck_121_ == 0)
{
v___x_111_ = v_v_88_;
v_isShared_112_ = v_isSharedCheck_121_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_node_109_);
lean_dec(v_v_88_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_121_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
size_t v___x_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_113_ = ((size_t)5ULL);
v___x_114_ = lean_usize_shift_right(v_x_75_, v___x_113_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_add(v_x_76_, v___x_115_);
v___x_117_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_node_109_, v___x_114_, v___x_116_, v_x_77_, v_x_78_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_117_);
v___x_119_ = v___x_111_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_92_ = v___x_119_;
goto v___jp_91_;
}
}
}
default: 
{
lean_object* v___x_122_; 
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_x_77_);
lean_ctor_set(v___x_122_, 1, v_x_78_);
v___y_92_ = v___x_122_;
goto v___jp_91_;
}
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_array_fset(v_xs_x27_90_, v_j_82_, v___y_92_);
lean_dec(v_j_82_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_93_);
v___x_95_ = v___x_86_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
else
{
lean_object* v_ks_125_; lean_object* v_vs_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_144_; 
v_ks_125_ = lean_ctor_get(v_x_74_, 0);
v_vs_126_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_144_ == 0)
{
v___x_128_ = v_x_74_;
v_isShared_129_ = v_isSharedCheck_144_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_vs_126_);
lean_inc(v_ks_125_);
lean_dec(v_x_74_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_144_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_ks_125_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_vs_126_);
v___x_131_ = v_reuseFailAlloc_143_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v_newNode_132_; size_t v___x_133_; uint8_t v___x_134_; 
v_newNode_132_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_131_, v_x_77_, v_x_78_);
v___x_133_ = ((size_t)7ULL);
v___x_134_ = lean_usize_dec_le(v___x_133_, v_x_76_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_132_);
v___x_136_ = lean_unsigned_to_nat(4u);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
lean_dec(v___x_135_);
if (v___x_137_ == 0)
{
lean_object* v_ks_138_; lean_object* v_vs_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_ks_138_ = lean_ctor_get(v_newNode_132_, 0);
lean_inc_ref(v_ks_138_);
v_vs_139_ = lean_ctor_get(v_newNode_132_, 1);
lean_inc_ref(v_vs_139_);
lean_dec_ref(v_newNode_132_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_76_, v_ks_138_, v_vs_139_, v___x_140_, v___x_141_);
lean_dec_ref(v_vs_139_);
lean_dec_ref(v_ks_138_);
return v___x_142_;
}
else
{
return v_newNode_132_;
}
}
else
{
return v_newNode_132_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_74_ = stack[0].m_obj;
size_t v_x_75_ = stack[1].m_num;
size_t v_x_76_ = stack[2].m_num;
lean_object* v_x_77_ = stack[3].m_obj;
lean_object* v_x_78_ = stack[4].m_obj;
lean_object* v_res_145_;
v_res_145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_74_, v_x_75_, v_x_76_, v_x_77_, v_x_78_);
stack->m_obj
 = v_res_145_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t v_depth_146_, lean_object* v_keys_147_, lean_object* v_vals_148_, lean_object* v_i_149_, lean_object* v_entries_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_array_get_size(v_keys_147_);
v___x_152_ = lean_nat_dec_lt(v_i_149_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec(v_i_149_);
return v_entries_150_;
}
else
{
lean_object* v_k_153_; lean_object* v_v_154_; uint64_t v___x_155_; size_t v_h_156_; size_t v___x_157_; lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v_h_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_k_153_ = lean_array_fget_borrowed(v_keys_147_, v_i_149_);
v_v_154_ = lean_array_fget_borrowed(v_vals_148_, v_i_149_);
v___x_155_ = l_Lean_instHashableMVarId_hash(v_k_153_);
v_h_156_ = lean_uint64_to_usize(v___x_155_);
v___x_157_ = ((size_t)5ULL);
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_sub(v_depth_146_, v___x_159_);
v___x_161_ = lean_usize_mul(v___x_157_, v___x_160_);
v_h_162_ = lean_usize_shift_right(v_h_156_, v___x_161_);
v___x_163_ = lean_nat_add(v_i_149_, v___x_158_);
lean_dec(v_i_149_);
lean_inc(v_v_154_);
lean_inc(v_k_153_);
v___x_164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_150_, v_h_162_, v_depth_146_, v_k_153_, v_v_154_);
v_i_149_ = v___x_163_;
v_entries_150_ = v___x_164_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_146_ = stack[0].m_num;
lean_object* v_keys_147_ = stack[1].m_obj;
lean_object* v_vals_148_ = stack[2].m_obj;
lean_object* v_i_149_ = stack[3].m_obj;
lean_object* v_entries_150_ = stack[4].m_obj;
lean_object* v_res_166_;
v_res_166_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_146_, v_keys_147_, v_vals_148_, v_i_149_, v_entries_150_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_depth_167_, lean_object* v_keys_168_, lean_object* v_vals_169_, lean_object* v_i_170_, lean_object* v_entries_171_){
_start:
{
size_t v_depth_boxed_172_; lean_object* v_res_173_; 
v_depth_boxed_172_ = lean_unbox_usize(v_depth_167_);
lean_dec(v_depth_167_);
v_res_173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_172_, v_keys_168_, v_vals_169_, v_i_170_, v_entries_171_);
lean_dec_ref(v_vals_169_);
lean_dec_ref(v_keys_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
size_t v_x_14612__boxed_179_; size_t v_x_14613__boxed_180_; lean_object* v_res_181_; 
v_x_14612__boxed_179_ = lean_unbox_usize(v_x_175_);
lean_dec(v_x_175_);
v_x_14613__boxed_180_ = lean_unbox_usize(v_x_176_);
lean_dec(v_x_176_);
v_res_181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_174_, v_x_14612__boxed_179_, v_x_14613__boxed_180_, v_x_177_, v_x_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
uint64_t v___x_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v___x_188_; 
v___x_185_ = l_Lean_instHashableMVarId_hash(v_x_183_);
v___x_186_ = lean_uint64_to_usize(v___x_185_);
v___x_187_ = ((size_t)1ULL);
v___x_188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_182_, v___x_186_, v___x_187_, v_x_183_, v_x_184_);
return v___x_188_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_189_, lean_object* v_val_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_mctx_194_; lean_object* v_cache_195_; lean_object* v_zetaDeltaFVarIds_196_; lean_object* v_postponed_197_; lean_object* v_diag_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_228_; 
v___x_193_ = lean_st_ref_take(v___y_191_);
v_mctx_194_ = lean_ctor_get(v___x_193_, 0);
v_cache_195_ = lean_ctor_get(v___x_193_, 1);
v_zetaDeltaFVarIds_196_ = lean_ctor_get(v___x_193_, 2);
v_postponed_197_ = lean_ctor_get(v___x_193_, 3);
v_diag_198_ = lean_ctor_get(v___x_193_, 4);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_228_ == 0)
{
v___x_200_ = v___x_193_;
v_isShared_201_ = v_isSharedCheck_228_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_diag_198_);
lean_inc(v_postponed_197_);
lean_inc(v_zetaDeltaFVarIds_196_);
lean_inc(v_cache_195_);
lean_inc(v_mctx_194_);
lean_dec(v___x_193_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_228_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_depth_202_; lean_object* v_levelAssignDepth_203_; lean_object* v_lmvarCounter_204_; lean_object* v_mvarCounter_205_; lean_object* v_lDecls_206_; lean_object* v_decls_207_; lean_object* v_userNames_208_; lean_object* v_lAssignment_209_; lean_object* v_eAssignment_210_; lean_object* v_dAssignment_211_; lean_object* v_instanceTypedMVars_212_; lean_object* v_synthNormMemo_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_227_; 
v_depth_202_ = lean_ctor_get(v_mctx_194_, 0);
v_levelAssignDepth_203_ = lean_ctor_get(v_mctx_194_, 1);
v_lmvarCounter_204_ = lean_ctor_get(v_mctx_194_, 2);
v_mvarCounter_205_ = lean_ctor_get(v_mctx_194_, 3);
v_lDecls_206_ = lean_ctor_get(v_mctx_194_, 4);
v_decls_207_ = lean_ctor_get(v_mctx_194_, 5);
v_userNames_208_ = lean_ctor_get(v_mctx_194_, 6);
v_lAssignment_209_ = lean_ctor_get(v_mctx_194_, 7);
v_eAssignment_210_ = lean_ctor_get(v_mctx_194_, 8);
v_dAssignment_211_ = lean_ctor_get(v_mctx_194_, 9);
v_instanceTypedMVars_212_ = lean_ctor_get(v_mctx_194_, 10);
v_synthNormMemo_213_ = lean_ctor_get(v_mctx_194_, 11);
v_isSharedCheck_227_ = !lean_is_exclusive(v_mctx_194_);
if (v_isSharedCheck_227_ == 0)
{
v___x_215_ = v_mctx_194_;
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_synthNormMemo_213_);
lean_inc(v_instanceTypedMVars_212_);
lean_inc(v_dAssignment_211_);
lean_inc(v_eAssignment_210_);
lean_inc(v_lAssignment_209_);
lean_inc(v_userNames_208_);
lean_inc(v_decls_207_);
lean_inc(v_lDecls_206_);
lean_inc(v_mvarCounter_205_);
lean_inc(v_lmvarCounter_204_);
lean_inc(v_levelAssignDepth_203_);
lean_inc(v_depth_202_);
lean_dec(v_mctx_194_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_227_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_217_ = lean_box(0);
v___x_218_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_210_, v_mvarId_189_, v_val_190_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 8, v___x_218_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_depth_202_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_levelAssignDepth_203_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_lmvarCounter_204_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_mvarCounter_205_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_lDecls_206_);
lean_ctor_set(v_reuseFailAlloc_226_, 5, v_decls_207_);
lean_ctor_set(v_reuseFailAlloc_226_, 6, v_userNames_208_);
lean_ctor_set(v_reuseFailAlloc_226_, 7, v_lAssignment_209_);
lean_ctor_set(v_reuseFailAlloc_226_, 8, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_226_, 9, v_dAssignment_211_);
lean_ctor_set(v_reuseFailAlloc_226_, 10, v_instanceTypedMVars_212_);
lean_ctor_set(v_reuseFailAlloc_226_, 11, v_synthNormMemo_213_);
v___x_220_ = v_reuseFailAlloc_226_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_220_);
v___x_222_ = v___x_200_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_cache_195_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_zetaDeltaFVarIds_196_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_postponed_197_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_diag_198_);
v___x_222_ = v_reuseFailAlloc_225_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_st_ref_put(v___y_191_, v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_217_);
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_189_ = stack[0].m_obj;
lean_object* v_val_190_ = stack[1].m_obj;
lean_object* v___y_191_ = stack[2].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_189_, v_val_190_, v___y_191_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_230_, lean_object* v_val_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_230_, v_val_231_, v___y_232_);
lean_dec(v___y_232_);
return v_res_234_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_keys_235_, lean_object* v_i_236_, lean_object* v_k_237_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_array_get_size(v_keys_235_);
v___x_239_ = lean_nat_dec_lt(v_i_236_, v___x_238_);
if (v___x_239_ == 0)
{
lean_dec(v_i_236_);
return v___x_239_;
}
else
{
lean_object* v_k_x27_240_; uint8_t v___x_241_; 
v_k_x27_240_ = lean_array_fget_borrowed(v_keys_235_, v_i_236_);
v___x_241_ = l_Lean_instBEqMVarId_beq(v_k_237_, v_k_x27_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_i_236_, v___x_242_);
lean_dec(v_i_236_);
v_i_236_ = v___x_243_;
goto _start;
}
else
{
lean_dec(v_i_236_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_235_ = stack[0].m_obj;
lean_object* v_i_236_ = stack[1].m_obj;
lean_object* v_k_237_ = stack[2].m_obj;
uint8_t v_res_245_;
v_res_245_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_235_, v_i_236_, v_k_237_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_keys_246_, lean_object* v_i_247_, lean_object* v_k_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_246_, v_i_247_, v_k_248_);
lean_dec(v_k_248_);
lean_dec_ref(v_keys_246_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_251_, size_t v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v_es_254_; lean_object* v___x_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v_j_258_; lean_object* v___x_259_; 
v_es_254_ = lean_ctor_get(v_x_251_, 0);
v___x_255_ = lean_box(2);
v___x_256_ = ((size_t)31ULL);
v___x_257_ = lean_usize_land(v_x_252_, v___x_256_);
v_j_258_ = lean_usize_to_nat(v___x_257_);
v___x_259_ = lean_array_get_borrowed(v___x_255_, v_es_254_, v_j_258_);
lean_dec(v_j_258_);
switch(lean_obj_tag(v___x_259_))
{
case 0:
{
lean_object* v_key_260_; uint8_t v___x_261_; 
v_key_260_ = lean_ctor_get(v___x_259_, 0);
v___x_261_ = l_Lean_instBEqMVarId_beq(v_x_253_, v_key_260_);
return v___x_261_;
}
case 1:
{
lean_object* v_node_262_; size_t v___x_263_; size_t v___x_264_; 
v_node_262_ = lean_ctor_get(v___x_259_, 0);
v___x_263_ = ((size_t)5ULL);
v___x_264_ = lean_usize_shift_right(v_x_252_, v___x_263_);
v_x_251_ = v_node_262_;
v_x_252_ = v___x_264_;
goto _start;
}
default: 
{
uint8_t v___x_266_; 
v___x_266_ = 0;
return v___x_266_;
}
}
}
else
{
lean_object* v_ks_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_ks_267_ = lean_ctor_get(v_x_251_, 0);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_267_, v___x_268_, v_x_253_);
return v___x_269_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_251_ = stack[0].m_obj;
size_t v_x_252_ = stack[1].m_num;
lean_object* v_x_253_ = stack[2].m_obj;
uint8_t v_res_270_;
v_res_270_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_251_, v_x_252_, v_x_253_);
stack->m_num = v_res_270_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
size_t v_x_14954__boxed_274_; uint8_t v_res_275_; lean_object* v_r_276_; 
v_x_14954__boxed_274_ = lean_unbox_usize(v_x_272_);
lean_dec(v_x_272_);
v_res_275_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_271_, v_x_14954__boxed_274_, v_x_273_);
lean_dec(v_x_273_);
lean_dec_ref(v_x_271_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint64_t v___x_279_; size_t v___x_280_; uint8_t v___x_281_; 
v___x_279_ = l_Lean_instHashableMVarId_hash(v_x_278_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_277_, v___x_280_, v_x_278_);
return v___x_281_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_277_ = stack[0].m_obj;
lean_object* v_x_278_ = stack[1].m_obj;
uint8_t v_res_282_;
v_res_282_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_277_, v_x_278_);
stack->m_num = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec_ref(v_x_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_eAssignment_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_290_ = lean_st_ref_get(v___y_288_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_eAssignment_292_ = lean_ctor_get(v_mctx_291_, 8);
lean_inc_ref(v_eAssignment_292_);
lean_dec_ref(v_mctx_291_);
v___x_293_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_292_, v_mvarId_287_);
lean_dec_ref(v_eAssignment_292_);
v___x_294_ = lean_box(v___x_293_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_287_ = stack[0].m_obj;
lean_object* v___y_288_ = stack[1].m_obj;
lean_object* v_res_296_;
v_res_296_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_287_, v___y_288_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec(v_mvarId_297_);
return v_res_300_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object* v___f_312_, lean_object* v_mv_313_, lean_object* v_val_314_, lean_object* v_tac_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___y_332_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_toCold_378_; lean_object* v_currRecDepth_379_; lean_object* v_ref_380_; uint16_t v_optionFlags_381_; uint8_t v_suppressElabErrors_382_; uint8_t v_isRecordingDeps_383_; lean_object* v___x_384_; uint8_t v_transparency_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v_ref_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_323_ = lean_box(0);
v___x_324_ = lean_box(0);
v___x_325_ = 1;
v___x_329_ = lean_box(1);
v___x_330_ = 0;
v___x_376_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2));
v___x_377_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_377_, 0, v___x_323_);
lean_ctor_set(v___x_377_, 1, v___x_324_);
lean_ctor_set(v___x_377_, 2, v___x_323_);
lean_ctor_set(v___x_377_, 3, v___f_312_);
lean_ctor_set(v___x_377_, 4, v___x_329_);
lean_ctor_set(v___x_377_, 5, v___x_329_);
lean_ctor_set(v___x_377_, 6, v___x_323_);
lean_ctor_set(v___x_377_, 7, v___x_376_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8, v___x_325_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 1, v___x_325_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 2, v___x_325_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 3, v___x_325_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 4, v___x_330_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 5, v___x_330_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 6, v___x_330_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 7, v___x_330_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 8, v___x_325_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 9, v___x_330_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*8 + 10, v___x_325_);
v_toCold_378_ = lean_ctor_get(v___y_320_, 0);
v_currRecDepth_379_ = lean_ctor_get(v___y_320_, 1);
v_ref_380_ = lean_ctor_get(v___y_320_, 2);
v_optionFlags_381_ = lean_ctor_get_uint16(v___y_320_, sizeof(void*)*3);
v_suppressElabErrors_382_ = lean_ctor_get_uint8(v___y_320_, sizeof(void*)*3 + 2);
v_isRecordingDeps_383_ = lean_ctor_get_uint8(v___y_320_, sizeof(void*)*3 + 3);
v___x_384_ = l_Lean_Meta_Context_config(v___y_318_);
v_transparency_385_ = lean_ctor_get_uint8(v___x_384_, 9);
lean_dec_ref(v___x_384_);
v___x_386_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3));
v___x_387_ = 1;
v_ref_388_ = l_Lean_replaceRef(v_val_314_, v_ref_380_);
lean_inc(v_currRecDepth_379_);
lean_inc_ref(v_toCold_378_);
v___x_389_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_389_, 0, v_toCold_378_);
lean_ctor_set(v___x_389_, 1, v_currRecDepth_379_);
lean_ctor_set(v___x_389_, 2, v_ref_388_);
lean_ctor_set_uint16(v___x_389_, sizeof(void*)*3, v_optionFlags_381_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 2, v_suppressElabErrors_382_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 3, v_isRecordingDeps_383_);
v___x_390_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_385_, v___x_387_);
if (v___x_390_ == 0)
{
lean_object* v_keyedConfig_391_; uint8_t v_trackZetaDelta_392_; lean_object* v_zetaDeltaSet_393_; lean_object* v_lctx_394_; lean_object* v_localInstances_395_; lean_object* v_defEqCtx_x3f_396_; lean_object* v_synthPendingDepth_397_; lean_object* v_customCanUnfoldPredicate_x3f_398_; uint8_t v_univApprox_399_; uint8_t v_inTypeClassResolution_400_; uint8_t v_cacheInferType_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_keyedConfig_391_ = lean_ctor_get(v___y_318_, 0);
v_trackZetaDelta_392_ = lean_ctor_get_uint8(v___y_318_, sizeof(void*)*7);
v_zetaDeltaSet_393_ = lean_ctor_get(v___y_318_, 1);
v_lctx_394_ = lean_ctor_get(v___y_318_, 2);
v_localInstances_395_ = lean_ctor_get(v___y_318_, 3);
v_defEqCtx_x3f_396_ = lean_ctor_get(v___y_318_, 4);
v_synthPendingDepth_397_ = lean_ctor_get(v___y_318_, 5);
v_customCanUnfoldPredicate_x3f_398_ = lean_ctor_get(v___y_318_, 6);
v_univApprox_399_ = lean_ctor_get_uint8(v___y_318_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_400_ = lean_ctor_get_uint8(v___y_318_, sizeof(void*)*7 + 2);
v_cacheInferType_401_ = lean_ctor_get_uint8(v___y_318_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_391_);
v___x_402_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_387_, v_keyedConfig_391_);
lean_inc(v_customCanUnfoldPredicate_x3f_398_);
lean_inc(v_synthPendingDepth_397_);
lean_inc(v_defEqCtx_x3f_396_);
lean_inc_ref(v_localInstances_395_);
lean_inc_ref(v_lctx_394_);
lean_inc(v_zetaDeltaSet_393_);
v___x_403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v_zetaDeltaSet_393_);
lean_ctor_set(v___x_403_, 2, v_lctx_394_);
lean_ctor_set(v___x_403_, 3, v_localInstances_395_);
lean_ctor_set(v___x_403_, 4, v_defEqCtx_x3f_396_);
lean_ctor_set(v___x_403_, 5, v_synthPendingDepth_397_);
lean_ctor_set(v___x_403_, 6, v_customCanUnfoldPredicate_x3f_398_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7, v_trackZetaDelta_392_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7 + 1, v_univApprox_399_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7 + 2, v_inTypeClassResolution_400_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*7 + 3, v_cacheInferType_401_);
lean_inc(v_mv_313_);
v___x_404_ = l_Lean_Elab_runTactic(v_mv_313_, v_tac_315_, v___x_377_, v___x_386_, v___x_403_, v___y_319_, v___x_389_, v___y_321_);
lean_dec_ref_known(v___x_389_, 3);
lean_dec_ref_known(v___x_403_, 7);
v___y_332_ = v___x_404_;
goto v___jp_331_;
}
else
{
lean_object* v___x_405_; 
lean_inc(v_mv_313_);
v___x_405_ = l_Lean_Elab_runTactic(v_mv_313_, v_tac_315_, v___x_377_, v___x_386_, v___y_318_, v___y_319_, v___x_389_, v___y_321_);
lean_dec_ref_known(v___x_389_, 3);
v___y_332_ = v___x_405_;
goto v___jp_331_;
}
v___jp_326_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__0));
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
v___jp_331_:
{
if (lean_obj_tag(v___y_332_) == 0)
{
lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref_known(v___y_332_, 1);
v___x_333_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mv_313_, v___y_319_);
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_367_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_367_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_367_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint8_t v___x_338_; 
v___x_338_ = lean_unbox(v_a_334_);
lean_dec(v_a_334_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_mv_313_);
v___x_339_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_339_);
v___x_341_ = v___x_336_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_343_; lean_object* v_a_344_; 
lean_del_object(v___x_336_);
v___x_343_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_mv_313_, v___y_319_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref(v___x_343_);
if (lean_obj_tag(v_a_344_) == 1)
{
lean_object* v_val_345_; lean_object* v___x_346_; 
v_val_345_ = lean_ctor_get(v_a_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v_a_344_, 1);
v___x_346_ = l_Lean_Meta_Sym_unfoldReducible(v_val_345_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = l_Lean_Meta_Sym_shareCommon(v_a_347_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mv_313_, v_a_349_, v___y_319_);
lean_dec_ref(v___x_350_);
goto v___jp_326_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_mv_313_);
v_a_351_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_348_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_348_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_mv_313_);
v_a_359_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_346_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_346_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_dec(v_a_344_);
lean_dec(v_mv_313_);
goto v___jp_326_;
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_mv_313_);
v_a_368_ = lean_ctor_get(v___y_332_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___y_332_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___y_332_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___y_332_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_312_ = stack[0].m_obj;
lean_object* v_mv_313_ = stack[1].m_obj;
lean_object* v_val_314_ = stack[2].m_obj;
lean_object* v_tac_315_ = stack[3].m_obj;
lean_object* v___y_316_ = stack[4].m_obj;
lean_object* v___y_317_ = stack[5].m_obj;
lean_object* v___y_318_ = stack[6].m_obj;
lean_object* v___y_319_ = stack[7].m_obj;
lean_object* v___y_320_ = stack[8].m_obj;
lean_object* v___y_321_ = stack[9].m_obj;
lean_object* v_res_406_;
v_res_406_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_312_, v_mv_313_, v_val_314_, v_tac_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_407_, lean_object* v_mv_408_, lean_object* v_val_409_, lean_object* v_tac_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_407_, v_mv_408_, v_val_409_, v_tac_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v_val_409_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
return v___x_421_;
}
else
{
lean_object* v_key_422_; lean_object* v_value_423_; lean_object* v_tail_424_; uint8_t v___x_425_; 
v_key_422_ = lean_ctor_get(v_x_420_, 0);
v_value_423_ = lean_ctor_get(v_x_420_, 1);
v_tail_424_ = lean_ctor_get(v_x_420_, 2);
v___x_425_ = lean_nat_dec_eq(v_key_422_, v_a_419_);
if (v___x_425_ == 0)
{
v_x_420_ = v_tail_424_;
goto _start;
}
else
{
lean_object* v___x_427_; 
lean_inc(v_value_423_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_value_423_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec(v_a_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_buckets_433_; lean_object* v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v_fold_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_buckets_433_ = lean_ctor_get(v_m_431_, 1);
v___x_434_ = lean_array_get_size(v_buckets_433_);
v___x_435_ = lean_uint64_of_nat(v_a_432_);
v___x_436_ = 32ULL;
v___x_437_ = lean_uint64_shift_right(v___x_435_, v___x_436_);
v_fold_438_ = lean_uint64_xor(v___x_435_, v___x_437_);
v___x_439_ = 16ULL;
v___x_440_ = lean_uint64_shift_right(v_fold_438_, v___x_439_);
v___x_441_ = lean_uint64_xor(v_fold_438_, v___x_440_);
v___x_442_ = lean_uint64_to_usize(v___x_441_);
v___x_443_ = lean_usize_of_nat(v___x_434_);
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_sub(v___x_443_, v___x_444_);
v___x_446_ = lean_usize_land(v___x_442_, v___x_445_);
v___x_447_ = lean_array_uget_borrowed(v_buckets_433_, v___x_446_);
v___x_448_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_432_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_m_449_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Array_mkArray0___redArg();
return v___x_503_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object* v_invariantAlts_516_, lean_object* v_n_517_, lean_object* v_mv_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___y_527_; uint8_t v___y_528_; lean_object* v___y_533_; lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_516_, v_n_517_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_618_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_618_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_618_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_618_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___f_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___f_551_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0));
v___x_552_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5));
lean_inc(v_val_547_);
v___x_553_ = l_Lean_Syntax_isOfKind(v_val_547_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7));
lean_inc(v_val_547_);
v___x_555_ = l_Lean_Syntax_isOfKind(v_val_547_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_558_; 
lean_dec(v_val_547_);
lean_dec(v_mv_518_);
v___x_556_ = lean_box(v___x_555_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_556_);
v___x_558_ = v___x_549_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = l_Lean_Syntax_getArg(v_val_547_, v___x_560_);
v___x_562_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9));
lean_inc(v___x_561_);
v___x_563_ = l_Lean_Syntax_isOfKind(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_566_; 
lean_dec(v___x_561_);
lean_dec(v_val_547_);
lean_dec(v_mv_518_);
v___x_564_ = lean_box(v___x_563_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_564_);
v___x_566_ = v___x_549_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
else
{
lean_object* v_ref_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_args_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_del_object(v___x_549_);
v_ref_568_ = lean_ctor_get(v_a_523_, 2);
v___x_569_ = l_Lean_Syntax_getArg(v___x_561_, v___x_560_);
lean_dec(v___x_561_);
v___x_570_ = lean_unsigned_to_nat(3u);
v___x_571_ = l_Lean_Syntax_getArg(v_val_547_, v___x_570_);
v_args_572_ = l_Lean_Syntax_getArgs(v___x_569_);
lean_dec(v___x_569_);
v___x_573_ = l_Lean_SourceInfo_fromRef(v_ref_568_, v___x_553_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11));
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_573_, 11);
v___x_576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14));
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16));
v___x_579_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18));
v___x_580_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20));
v___x_581_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21));
v___x_582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_573_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22);
v___x_584_ = l_Array_append___redArg(v___x_583_, v_args_572_);
lean_dec_ref(v_args_572_);
v___x_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_573_);
lean_ctor_set(v___x_585_, 1, v___x_579_);
lean_ctor_set(v___x_585_, 2, v___x_584_);
v___x_586_ = l_Lean_Syntax_node2(v___x_573_, v___x_580_, v___x_582_, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23));
v___x_588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_573_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_590_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
v___x_591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_573_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
v___x_592_ = l_Lean_Syntax_node2(v___x_573_, v___x_590_, v___x_591_, v___x_571_);
v___x_593_ = l_Lean_Syntax_node3(v___x_573_, v___x_579_, v___x_586_, v___x_588_, v___x_592_);
v___x_594_ = l_Lean_Syntax_node1(v___x_573_, v___x_578_, v___x_593_);
v___x_595_ = l_Lean_Syntax_node1(v___x_573_, v___x_577_, v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26));
v___x_597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_573_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_Syntax_node3(v___x_573_, v___x_574_, v___x_576_, v___x_595_, v___x_597_);
v___x_599_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_551_, v_mv_518_, v_val_547_, v___x_598_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_val_547_);
v___y_533_ = v___x_599_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = l_Lean_Syntax_getArg(v_val_547_, v___x_600_);
v___x_602_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28));
v___x_603_ = l_Lean_Syntax_isOfKind(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_606_; 
lean_dec(v_val_547_);
lean_dec(v_mv_518_);
v___x_604_ = lean_box(v___x_603_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_604_);
v___x_606_ = v___x_549_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v_ref_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_del_object(v___x_549_);
v_ref_608_ = lean_ctor_get(v_a_523_, 2);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = l_Lean_Syntax_getArg(v_val_547_, v___x_609_);
v___x_611_ = 0;
v___x_612_ = l_Lean_SourceInfo_fromRef(v_ref_608_, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_614_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
lean_inc(v___x_612_);
v___x_615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_612_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
v___x_616_ = l_Lean_Syntax_node2(v___x_612_, v___x_614_, v___x_615_, v___x_610_);
v___x_617_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_551_, v_mv_518_, v_val_547_, v___x_616_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_val_547_);
v___y_533_ = v___x_617_;
goto v___jp_532_;
}
}
}
}
else
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v___x_546_);
lean_dec(v_mv_518_);
v___x_619_ = 0;
v___x_620_ = lean_box(v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
v___jp_526_:
{
if (v___y_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec_ref(v___y_527_);
v___x_529_ = lean_box(v___y_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v___y_527_);
return v___x_531_;
}
}
v___jp_532_:
{
if (lean_obj_tag(v___y_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_a_534_ = lean_ctor_get(v___y_533_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___y_533_);
if (v_isSharedCheck_542_ == 0)
{
v___x_536_ = v___y_533_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___y_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_a_538_; lean_object* v___x_540_; 
v_a_538_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_a_538_);
lean_dec(v_a_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_a_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_543_; uint8_t v___x_544_; 
v_a_543_ = lean_ctor_get(v___y_533_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___y_533_, 1);
v___x_544_ = l_Lean_Exception_isInterrupt(v_a_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
lean_inc(v_a_543_);
v___x_545_ = l_Lean_Exception_isRuntime(v_a_543_);
v___y_527_ = v_a_543_;
v___y_528_ = v___x_545_;
goto v___jp_526_;
}
else
{
v___y_527_ = v_a_543_;
v___y_528_ = v___x_544_;
goto v___jp_526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_elabInvariant_0interp(lean_interpreter_value* stack)
{
lean_object* v_invariantAlts_516_ = stack[0].m_obj;
lean_object* v_n_517_ = stack[1].m_obj;
lean_object* v_mv_518_ = stack[2].m_obj;
lean_object* v_a_519_ = stack[3].m_obj;
lean_object* v_a_520_ = stack[4].m_obj;
lean_object* v_a_521_ = stack[5].m_obj;
lean_object* v_a_522_ = stack[6].m_obj;
lean_object* v_a_523_ = stack[7].m_obj;
lean_object* v_a_524_ = stack[8].m_obj;
lean_object* v_res_622_;
v_res_622_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_516_, v_n_517_, v_mv_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_623_, lean_object* v_n_624_, lean_object* v_mv_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_623_, v_n_624_, v_mv_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_n_624_);
lean_dec_ref(v_invariantAlts_623_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_634_, lean_object* v_m_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_635_, v_a_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_638_, lean_object* v_m_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(v_00_u03b2_638_, v_m_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_m_639_);
return v_res_641_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_642_, v___y_646_);
return v___x_650_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_642_ = stack[0].m_obj;
lean_object* v___y_643_ = stack[1].m_obj;
lean_object* v___y_644_ = stack[2].m_obj;
lean_object* v___y_645_ = stack[3].m_obj;
lean_object* v___y_646_ = stack[4].m_obj;
lean_object* v___y_647_ = stack[5].m_obj;
lean_object* v___y_648_ = stack[6].m_obj;
lean_object* v_res_651_;
v_res_651_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_mvarId_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_mvarId_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v_mvarId_652_);
return v_res_660_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_661_, lean_object* v_val_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_661_, v_val_662_, v___y_666_);
return v___x_670_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_661_ = stack[0].m_obj;
lean_object* v_val_662_ = stack[1].m_obj;
lean_object* v___y_663_ = stack[2].m_obj;
lean_object* v___y_664_ = stack[3].m_obj;
lean_object* v___y_665_ = stack[4].m_obj;
lean_object* v___y_666_ = stack[5].m_obj;
lean_object* v___y_667_ = stack[6].m_obj;
lean_object* v___y_668_ = stack[7].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_661_, v_val_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_672_, lean_object* v_val_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_672_, v_val_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_682_, lean_object* v_a_683_, lean_object* v_x_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_683_, v_x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_686_, lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_686_, v_a_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec(v_a_687_);
return v_res_689_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_691_, v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_691_ = stack[1].m_obj;
lean_object* v_x_692_ = stack[2].m_obj;
uint8_t v_res_694_;
v_res_694_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_box(0), v_x_691_, v_x_692_);
stack->m_num = v_res_694_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_695_, v_x_696_, v_x_697_);
lean_dec(v_x_697_);
lean_dec_ref(v_x_696_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_701_, v_x_702_, v_x_703_);
return v___x_704_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_705_, lean_object* v_x_706_, size_t v_x_707_, lean_object* v_x_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_706_, v_x_707_, v_x_708_);
return v___x_709_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_706_ = stack[1].m_obj;
size_t v_x_707_ = stack[2].m_num;
lean_object* v_x_708_ = stack[3].m_obj;
uint8_t v_res_710_;
v_res_710_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_box(0), v_x_706_, v_x_707_, v_x_708_);
stack->m_num = v_res_710_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_711_, lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
size_t v_x_16083__boxed_715_; uint8_t v_res_716_; lean_object* v_r_717_; 
v_x_16083__boxed_715_ = lean_unbox_usize(v_x_713_);
lean_dec(v_x_713_);
v_res_716_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_711_, v_x_712_, v_x_16083__boxed_715_, v_x_714_);
lean_dec(v_x_714_);
lean_dec_ref(v_x_712_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, size_t v_x_720_, size_t v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_719_, v_x_720_, v_x_721_, v_x_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_719_ = stack[1].m_obj;
size_t v_x_720_ = stack[2].m_num;
size_t v_x_721_ = stack[3].m_num;
lean_object* v_x_722_ = stack[4].m_obj;
lean_object* v_x_723_ = stack[5].m_obj;
lean_object* v_res_725_;
v_res_725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_box(0), v_x_719_, v_x_720_, v_x_721_, v_x_722_, v_x_723_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
size_t v_x_16101__boxed_732_; size_t v_x_16102__boxed_733_; lean_object* v_res_734_; 
v_x_16101__boxed_732_ = lean_unbox_usize(v_x_728_);
lean_dec(v_x_728_);
v_x_16102__boxed_733_ = lean_unbox_usize(v_x_729_);
lean_dec(v_x_729_);
v_res_734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_726_, v_x_727_, v_x_16101__boxed_732_, v_x_16102__boxed_733_, v_x_730_, v_x_731_);
return v_res_734_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_735_, lean_object* v_keys_736_, lean_object* v_vals_737_, lean_object* v_heq_738_, lean_object* v_i_739_, lean_object* v_k_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_736_, v_i_739_, v_k_740_);
return v___x_741_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_736_ = stack[1].m_obj;
lean_object* v_vals_737_ = stack[2].m_obj;
lean_object* v_i_739_ = stack[4].m_obj;
lean_object* v_k_740_ = stack[5].m_obj;
uint8_t v_res_742_;
v_res_742_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_box(0), v_keys_736_, v_vals_737_, lean_box(0), v_i_739_, v_k_740_);
stack->m_num = v_res_742_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_743_, lean_object* v_keys_744_, lean_object* v_vals_745_, lean_object* v_heq_746_, lean_object* v_i_747_, lean_object* v_k_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_743_, v_keys_744_, v_vals_745_, v_heq_746_, v_i_747_, v_k_748_);
lean_dec(v_k_748_);
lean_dec_ref(v_vals_745_);
lean_dec_ref(v_keys_744_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_751_, lean_object* v_n_752_, lean_object* v_k_753_, lean_object* v_v_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_752_, v_k_753_, v_v_754_);
return v___x_755_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_756_, size_t v_depth_757_, lean_object* v_keys_758_, lean_object* v_vals_759_, lean_object* v_heq_760_, lean_object* v_i_761_, lean_object* v_entries_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_757_, v_keys_758_, v_vals_759_, v_i_761_, v_entries_762_);
return v___x_763_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
size_t v_depth_757_ = stack[1].m_num;
lean_object* v_keys_758_ = stack[2].m_obj;
lean_object* v_vals_759_ = stack[3].m_obj;
lean_object* v_i_761_ = stack[5].m_obj;
lean_object* v_entries_762_ = stack[6].m_obj;
lean_object* v_res_764_;
v_res_764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_box(0), v_depth_757_, v_keys_758_, v_vals_759_, lean_box(0), v_i_761_, v_entries_762_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_765_, lean_object* v_depth_766_, lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_heq_769_, lean_object* v_i_770_, lean_object* v_entries_771_){
_start:
{
size_t v_depth_boxed_772_; lean_object* v_res_773_; 
v_depth_boxed_772_ = lean_unbox_usize(v_depth_766_);
lean_dec(v_depth_766_);
v_res_773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_765_, v_depth_boxed_772_, v_keys_767_, v_vals_768_, v_heq_769_, v_i_770_, v_entries_771_);
lean_dec_ref(v_vals_768_);
lean_dec_ref(v_keys_767_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_775_, v_x_776_, v_x_777_, v_x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
return v_x_780_;
}
else
{
lean_object* v_key_782_; lean_object* v_value_783_; lean_object* v_tail_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_807_; 
v_key_782_ = lean_ctor_get(v_x_781_, 0);
v_value_783_ = lean_ctor_get(v_x_781_, 1);
v_tail_784_ = lean_ctor_get(v_x_781_, 2);
v_isSharedCheck_807_ = !lean_is_exclusive(v_x_781_);
if (v_isSharedCheck_807_ == 0)
{
v___x_786_ = v_x_781_;
v_isShared_787_ = v_isSharedCheck_807_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_tail_784_);
lean_inc(v_value_783_);
lean_inc(v_key_782_);
lean_dec(v_x_781_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_807_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v_fold_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_788_ = lean_array_get_size(v_x_780_);
v___x_789_ = lean_uint64_of_nat(v_key_782_);
v___x_790_ = 32ULL;
v___x_791_ = lean_uint64_shift_right(v___x_789_, v___x_790_);
v_fold_792_ = lean_uint64_xor(v___x_789_, v___x_791_);
v___x_793_ = 16ULL;
v___x_794_ = lean_uint64_shift_right(v_fold_792_, v___x_793_);
v___x_795_ = lean_uint64_xor(v_fold_792_, v___x_794_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = lean_usize_of_nat(v___x_788_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_sub(v___x_797_, v___x_798_);
v___x_800_ = lean_usize_land(v___x_796_, v___x_799_);
v___x_801_ = lean_array_uget_borrowed(v_x_780_, v___x_800_);
lean_inc(v___x_801_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 2, v___x_801_);
v___x_803_ = v___x_786_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_key_782_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_value_783_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v___x_801_);
v___x_803_ = v_reuseFailAlloc_806_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; 
v___x_804_ = lean_array_uset(v_x_780_, v___x_800_, v___x_803_);
v_x_780_ = v___x_804_;
v_x_781_ = v_tail_784_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_808_, lean_object* v_source_809_, lean_object* v_target_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_source_809_);
v___x_812_ = lean_nat_dec_lt(v_i_808_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec_ref(v_source_809_);
lean_dec(v_i_808_);
return v_target_810_;
}
else
{
lean_object* v_es_813_; lean_object* v___x_814_; lean_object* v_source_815_; lean_object* v_target_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_es_813_ = lean_array_fget(v_source_809_, v_i_808_);
v___x_814_ = lean_box(0);
v_source_815_ = lean_array_fset(v_source_809_, v_i_808_, v___x_814_);
v_target_816_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_810_, v_es_813_);
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_i_808_, v___x_817_);
lean_dec(v_i_808_);
v_i_808_ = v___x_818_;
v_source_809_ = v_source_815_;
v_target_810_ = v_target_816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_nbuckets_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_821_ = lean_array_get_size(v_data_820_);
v___x_822_ = lean_unsigned_to_nat(2u);
v_nbuckets_823_ = lean_nat_mul(v___x_821_, v___x_822_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_box(0);
v___x_826_ = lean_mk_array(v_nbuckets_823_, v___x_825_);
v___x_827_ = lean_array_propagate_mark(v_data_820_, v___x_826_);
v___x_828_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_824_, v_data_820_, v___x_827_);
return v___x_828_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
uint8_t v___x_831_; 
v___x_831_ = 0;
return v___x_831_;
}
else
{
lean_object* v_key_832_; lean_object* v_tail_833_; uint8_t v___x_834_; 
v_key_832_ = lean_ctor_get(v_x_830_, 0);
v_tail_833_ = lean_ctor_get(v_x_830_, 2);
v___x_834_ = lean_nat_dec_eq(v_key_832_, v_a_829_);
if (v___x_834_ == 0)
{
v_x_830_ = v_tail_833_;
goto _start;
}
else
{
return v___x_834_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_829_ = stack[0].m_obj;
lean_object* v_x_830_ = stack[1].m_obj;
uint8_t v_res_836_;
v_res_836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_829_, v_x_830_);
stack->m_num = v_res_836_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_837_, v_x_838_);
lean_dec(v_x_838_);
lean_dec(v_a_837_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_size_844_; lean_object* v_buckets_845_; lean_object* v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v_fold_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v_bkt_859_; uint8_t v___x_860_; 
v_size_844_ = lean_ctor_get(v_m_841_, 0);
v_buckets_845_ = lean_ctor_get(v_m_841_, 1);
v___x_846_ = lean_array_get_size(v_buckets_845_);
v___x_847_ = lean_uint64_of_nat(v_a_842_);
v___x_848_ = 32ULL;
v___x_849_ = lean_uint64_shift_right(v___x_847_, v___x_848_);
v_fold_850_ = lean_uint64_xor(v___x_847_, v___x_849_);
v___x_851_ = 16ULL;
v___x_852_ = lean_uint64_shift_right(v_fold_850_, v___x_851_);
v___x_853_ = lean_uint64_xor(v_fold_850_, v___x_852_);
v___x_854_ = lean_uint64_to_usize(v___x_853_);
v___x_855_ = lean_usize_of_nat(v___x_846_);
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_sub(v___x_855_, v___x_856_);
v___x_858_ = lean_usize_land(v___x_854_, v___x_857_);
v_bkt_859_ = lean_array_uget_borrowed(v_buckets_845_, v___x_858_);
v___x_860_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_842_, v_bkt_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_881_; 
lean_inc_ref(v_buckets_845_);
lean_inc(v_size_844_);
v_isSharedCheck_881_ = !lean_is_exclusive(v_m_841_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; lean_object* v_unused_883_; 
v_unused_882_ = lean_ctor_get(v_m_841_, 1);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_m_841_, 0);
lean_dec(v_unused_883_);
v___x_862_ = v_m_841_;
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_m_841_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_881_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v_size_x27_865_; lean_object* v___x_866_; lean_object* v_buckets_x27_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_864_ = lean_unsigned_to_nat(1u);
v_size_x27_865_ = lean_nat_add(v_size_844_, v___x_864_);
lean_dec(v_size_844_);
lean_inc(v_bkt_859_);
v___x_866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_866_, 0, v_a_842_);
lean_ctor_set(v___x_866_, 1, v_b_843_);
lean_ctor_set(v___x_866_, 2, v_bkt_859_);
v_buckets_x27_867_ = lean_array_uset(v_buckets_845_, v___x_858_, v___x_866_);
v___x_868_ = lean_unsigned_to_nat(4u);
v___x_869_ = lean_nat_mul(v_size_x27_865_, v___x_868_);
v___x_870_ = lean_unsigned_to_nat(3u);
v___x_871_ = lean_nat_div(v___x_869_, v___x_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_array_get_size(v_buckets_x27_867_);
v___x_873_ = lean_nat_dec_le(v___x_871_, v___x_872_);
lean_dec(v___x_871_);
if (v___x_873_ == 0)
{
lean_object* v_val_874_; lean_object* v___x_876_; 
v_val_874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_867_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_val_874_);
lean_ctor_set(v___x_862_, 0, v_size_x27_865_);
v___x_876_ = v___x_862_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_size_x27_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_val_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_879_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_buckets_x27_867_);
lean_ctor_set(v___x_862_, 0, v_size_x27_865_);
v___x_879_ = v___x_862_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_size_x27_865_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_buckets_x27_867_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_dec(v_b_843_);
lean_dec(v_a_842_);
return v_m_841_;
}
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_884_, lean_object* v_as_x27_885_, lean_object* v_b_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
if (lean_obj_tag(v_as_x27_885_) == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v___x_884_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_b_886_);
return v___x_896_;
}
else
{
lean_object* v_head_897_; lean_object* v_tail_898_; lean_object* v___x_899_; 
v_head_897_ = lean_ctor_get(v_as_x27_885_, 0);
v_tail_898_ = lean_ctor_get(v_as_x27_885_, 1);
lean_inc(v_head_897_);
v___x_899_ = l_Lean_MVarId_getType(v_head_897_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; uint8_t v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
lean_inc_ref(v___x_884_);
v___x_901_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_884_, v_a_900_);
lean_dec(v_a_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
lean_inc(v_head_897_);
v___x_902_ = lean_array_push(v_b_886_, v_head_897_);
v_as_x27_885_ = v_tail_898_;
v_b_886_ = v___x_902_;
goto _start;
}
else
{
lean_object* v___x_904_; lean_object* v_invariants_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_specBackwardRuleCache_910_; lean_object* v_splitBackwardRuleCache_911_; lean_object* v_latticeBackwardRuleCache_912_; lean_object* v_frameBackwardRuleCache_913_; lean_object* v_frameDB_914_; lean_object* v_invariants_915_; lean_object* v_vcs_916_; lean_object* v_simpState_917_; lean_object* v_fuel_918_; lean_object* v_inlineHandledInvariants_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_973_; 
v___x_904_ = lean_st_ref_get(v___y_888_);
v_invariants_905_ = lean_ctor_get(v___x_904_, 5);
lean_inc_ref(v_invariants_905_);
lean_dec(v___x_904_);
v___x_906_ = lean_array_get_size(v_invariants_905_);
lean_dec_ref(v_invariants_905_);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v___x_906_, v___x_907_);
v___x_909_ = lean_st_ref_take(v___y_888_);
v_specBackwardRuleCache_910_ = lean_ctor_get(v___x_909_, 0);
v_splitBackwardRuleCache_911_ = lean_ctor_get(v___x_909_, 1);
v_latticeBackwardRuleCache_912_ = lean_ctor_get(v___x_909_, 2);
v_frameBackwardRuleCache_913_ = lean_ctor_get(v___x_909_, 3);
v_frameDB_914_ = lean_ctor_get(v___x_909_, 4);
v_invariants_915_ = lean_ctor_get(v___x_909_, 5);
v_vcs_916_ = lean_ctor_get(v___x_909_, 6);
v_simpState_917_ = lean_ctor_get(v___x_909_, 7);
v_fuel_918_ = lean_ctor_get(v___x_909_, 8);
v_inlineHandledInvariants_919_ = lean_ctor_get(v___x_909_, 9);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_973_ == 0)
{
v___x_921_ = v___x_909_;
v_isShared_922_ = v_isSharedCheck_973_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_inlineHandledInvariants_919_);
lean_inc(v_fuel_918_);
lean_inc(v_simpState_917_);
lean_inc(v_vcs_916_);
lean_inc(v_invariants_915_);
lean_inc(v_frameDB_914_);
lean_inc(v_frameBackwardRuleCache_913_);
lean_inc(v_latticeBackwardRuleCache_912_);
lean_inc(v_splitBackwardRuleCache_911_);
lean_inc(v_specBackwardRuleCache_910_);
lean_dec(v___x_909_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_973_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_inc(v_head_897_);
v___x_923_ = lean_array_push(v_invariants_915_, v_head_897_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 5, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_specBackwardRuleCache_910_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_splitBackwardRuleCache_911_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_latticeBackwardRuleCache_912_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_frameBackwardRuleCache_913_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_frameDB_914_);
lean_ctor_set(v_reuseFailAlloc_972_, 5, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_972_, 6, v_vcs_916_);
lean_ctor_set(v_reuseFailAlloc_972_, 7, v_simpState_917_);
lean_ctor_set(v_reuseFailAlloc_972_, 8, v_fuel_918_);
lean_ctor_set(v_reuseFailAlloc_972_, 9, v_inlineHandledInvariants_919_);
v___x_925_ = v_reuseFailAlloc_972_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; lean_object* v_invariantAlts_927_; lean_object* v___x_928_; 
v___x_926_ = lean_st_ref_put(v___y_888_, v___x_925_);
v_invariantAlts_927_ = lean_ctor_get(v___y_887_, 3);
lean_inc(v_head_897_);
v___x_928_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_927_, v___x_908_, v_head_897_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_930_ == 0)
{
uint8_t v___x_931_; lean_object* v___x_932_; 
lean_dec(v___x_908_);
v___x_931_ = 2;
lean_inc(v_head_897_);
v___x_932_ = l_Lean_MVarId_setKind___redArg(v_head_897_, v___x_931_, v___y_892_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_dec_ref_known(v___x_932_, 1);
v_as_x27_885_ = v_tail_898_;
goto _start;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_b_886_);
lean_dec_ref(v___x_884_);
v_a_934_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_932_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_932_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v___x_942_; lean_object* v_specBackwardRuleCache_943_; lean_object* v_splitBackwardRuleCache_944_; lean_object* v_latticeBackwardRuleCache_945_; lean_object* v_frameBackwardRuleCache_946_; lean_object* v_frameDB_947_; lean_object* v_invariants_948_; lean_object* v_vcs_949_; lean_object* v_simpState_950_; lean_object* v_fuel_951_; lean_object* v_inlineHandledInvariants_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_963_; 
v___x_942_ = lean_st_ref_take(v___y_888_);
v_specBackwardRuleCache_943_ = lean_ctor_get(v___x_942_, 0);
v_splitBackwardRuleCache_944_ = lean_ctor_get(v___x_942_, 1);
v_latticeBackwardRuleCache_945_ = lean_ctor_get(v___x_942_, 2);
v_frameBackwardRuleCache_946_ = lean_ctor_get(v___x_942_, 3);
v_frameDB_947_ = lean_ctor_get(v___x_942_, 4);
v_invariants_948_ = lean_ctor_get(v___x_942_, 5);
v_vcs_949_ = lean_ctor_get(v___x_942_, 6);
v_simpState_950_ = lean_ctor_get(v___x_942_, 7);
v_fuel_951_ = lean_ctor_get(v___x_942_, 8);
v_inlineHandledInvariants_952_ = lean_ctor_get(v___x_942_, 9);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_963_ == 0)
{
v___x_954_ = v___x_942_;
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_inlineHandledInvariants_952_);
lean_inc(v_fuel_951_);
lean_inc(v_simpState_950_);
lean_inc(v_vcs_949_);
lean_inc(v_invariants_948_);
lean_inc(v_frameDB_947_);
lean_inc(v_frameBackwardRuleCache_946_);
lean_inc(v_latticeBackwardRuleCache_945_);
lean_inc(v_splitBackwardRuleCache_944_);
lean_inc(v_specBackwardRuleCache_943_);
lean_dec(v___x_942_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_956_ = lean_box(0);
v___x_957_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_952_, v___x_908_, v___x_956_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 9, v___x_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_specBackwardRuleCache_943_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_splitBackwardRuleCache_944_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_latticeBackwardRuleCache_945_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_frameBackwardRuleCache_946_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_frameDB_947_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v_invariants_948_);
lean_ctor_set(v_reuseFailAlloc_962_, 6, v_vcs_949_);
lean_ctor_set(v_reuseFailAlloc_962_, 7, v_simpState_950_);
lean_ctor_set(v_reuseFailAlloc_962_, 8, v_fuel_951_);
lean_ctor_set(v_reuseFailAlloc_962_, 9, v___x_957_);
v___x_959_ = v_reuseFailAlloc_962_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; 
v___x_960_ = lean_st_ref_put(v___y_888_, v___x_959_);
v_as_x27_885_ = v_tail_898_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v___x_908_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v___x_884_);
v_a_964_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_928_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_928_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v_b_886_);
lean_dec_ref(v___x_884_);
v_a_974_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_899_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_899_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_884_ = stack[0].m_obj;
lean_object* v_as_x27_885_ = stack[1].m_obj;
lean_object* v_b_886_ = stack[2].m_obj;
lean_object* v___y_887_ = stack[3].m_obj;
lean_object* v___y_888_ = stack[4].m_obj;
lean_object* v___y_889_ = stack[5].m_obj;
lean_object* v___y_890_ = stack[6].m_obj;
lean_object* v___y_891_ = stack[7].m_obj;
lean_object* v___y_892_ = stack[8].m_obj;
lean_object* v___y_893_ = stack[9].m_obj;
lean_object* v___y_894_ = stack[10].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_884_, v_as_x27_885_, v_b_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_983_, lean_object* v_as_x27_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_983_, v_as_x27_984_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_as_x27_984_);
return v_res_995_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1011_ = lean_st_ref_get(v_a_1009_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1014_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_1012_, v_subgoals_998_, v___x_1013_, v_a_999_, v_a_1000_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v___x_1014_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_0interp(lean_interpreter_value* stack)
{
lean_object* v_subgoals_998_ = stack[0].m_obj;
lean_object* v_a_999_ = stack[1].m_obj;
lean_object* v_a_1000_ = stack[2].m_obj;
lean_object* v_a_1001_ = stack[3].m_obj;
lean_object* v_a_1002_ = stack[4].m_obj;
lean_object* v_a_1003_ = stack[5].m_obj;
lean_object* v_a_1004_ = stack[6].m_obj;
lean_object* v_a_1005_ = stack[7].m_obj;
lean_object* v_a_1006_ = stack[8].m_obj;
lean_object* v_a_1007_ = stack[9].m_obj;
lean_object* v_a_1008_ = stack[10].m_obj;
lean_object* v_a_1009_ = stack[11].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_subgoals_1016_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1030_, lean_object* v_m_1031_, lean_object* v_a_1032_, lean_object* v_b_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1031_, v_a_1032_, v_b_1033_);
return v___x_1034_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1035_, lean_object* v_as_1036_, lean_object* v_as_x27_1037_, lean_object* v_b_1038_, lean_object* v_a_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1035_, v_as_x27_1037_, v_b_1038_, v___y_1040_, v___y_1041_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1035_ = stack[0].m_obj;
lean_object* v_as_1036_ = stack[1].m_obj;
lean_object* v_as_x27_1037_ = stack[2].m_obj;
lean_object* v_b_1038_ = stack[3].m_obj;
lean_object* v___y_1040_ = stack[5].m_obj;
lean_object* v___y_1041_ = stack[6].m_obj;
lean_object* v___y_1042_ = stack[7].m_obj;
lean_object* v___y_1043_ = stack[8].m_obj;
lean_object* v___y_1044_ = stack[9].m_obj;
lean_object* v___y_1045_ = stack[10].m_obj;
lean_object* v___y_1046_ = stack[11].m_obj;
lean_object* v___y_1047_ = stack[12].m_obj;
lean_object* v___y_1048_ = stack[13].m_obj;
lean_object* v___y_1049_ = stack[14].m_obj;
lean_object* v___y_1050_ = stack[15].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(v___x_1035_, v_as_1036_, v_as_x27_1037_, v_b_1038_, lean_box(0), v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1054_ = _args[0];
lean_object* v_as_1055_ = _args[1];
lean_object* v_as_x27_1056_ = _args[2];
lean_object* v_b_1057_ = _args[3];
lean_object* v_a_1058_ = _args[4];
lean_object* v___y_1059_ = _args[5];
lean_object* v___y_1060_ = _args[6];
lean_object* v___y_1061_ = _args[7];
lean_object* v___y_1062_ = _args[8];
lean_object* v___y_1063_ = _args[9];
lean_object* v___y_1064_ = _args[10];
lean_object* v___y_1065_ = _args[11];
lean_object* v___y_1066_ = _args[12];
lean_object* v___y_1067_ = _args[13];
lean_object* v___y_1068_ = _args[14];
lean_object* v___y_1069_ = _args[15];
lean_object* v___y_1070_ = _args[16];
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(v___x_1054_, v_as_1055_, v_as_x27_1056_, v_b_1057_, v_a_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v_as_x27_1056_);
lean_dec(v_as_1055_);
return v_res_1071_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1072_, lean_object* v_a_1073_, lean_object* v_x_1074_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1073_, v_x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1073_ = stack[1].m_obj;
lean_object* v_x_1074_ = stack[2].m_obj;
uint8_t v_res_1076_;
v_res_1076_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_box(0), v_a_1073_, v_x_1074_);
stack->m_num = v_res_1076_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1077_, lean_object* v_a_1078_, lean_object* v_x_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1077_, v_a_1078_, v_x_1079_);
lean_dec(v_x_1079_);
lean_dec(v_a_1078_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1082_, lean_object* v_data_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1085_, lean_object* v_i_1086_, lean_object* v_source_1087_, lean_object* v_target_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1086_, v_source_1087_, v_target_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_toGoalState_1107_; lean_object* v_mvarId_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1204_; 
v_toGoalState_1107_ = lean_ctor_get(v_goal_1094_, 0);
v_mvarId_1108_ = lean_ctor_get(v_goal_1094_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_goal_1094_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1110_ = v_goal_1094_;
v_isShared_1111_ = v_isSharedCheck_1204_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_mvarId_1108_);
lean_inc(v_toGoalState_1107_);
lean_dec(v_goal_1094_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1204_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1108_, v_a_1095_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_a_1113_);
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_toGoalState_1107_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_a_1113_);
v___x_1115_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v___x_1115_, v_a_1095_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1186_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1186_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1186_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_toGoalState_1121_; uint8_t v_inconsistent_1122_; 
v_toGoalState_1121_ = lean_ctor_get(v_a_1117_, 0);
lean_inc_ref(v_toGoalState_1121_);
v_inconsistent_1122_ = lean_ctor_get_uint8(v_toGoalState_1121_, sizeof(void*)*17);
if (v_inconsistent_1122_ == 0)
{
lean_object* v_mvarId_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1180_; 
lean_del_object(v___x_1119_);
v_mvarId_1123_ = lean_ctor_get(v_a_1117_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_a_1117_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_a_1117_, 0);
lean_dec(v_unused_1181_);
v___x_1125_ = v_a_1117_;
v_isShared_1126_ = v_isSharedCheck_1180_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_mvarId_1123_);
lean_dec(v_a_1117_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1180_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_mvarId_1123_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1171_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1171_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1171_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
if (lean_obj_tag(v_a_1128_) == 1)
{
lean_object* v_val_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; 
lean_del_object(v___x_1130_);
v_val_1132_ = lean_ctor_get(v_a_1128_, 0);
lean_inc_n(v_val_1132_, 2);
lean_dec_ref_known(v_a_1128_, 1);
v___x_1133_ = 2;
v___x_1134_ = l_Lean_MVarId_setKind___redArg(v_val_1132_, v___x_1133_, v_a_1103_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1165_; 
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1134_, 0);
lean_dec(v_unused_1166_);
v___x_1136_ = v___x_1134_;
v_isShared_1137_ = v_isSharedCheck_1165_;
goto v_resetjp_1135_;
}
else
{
lean_dec(v___x_1134_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1165_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v_specBackwardRuleCache_1139_; lean_object* v_splitBackwardRuleCache_1140_; lean_object* v_latticeBackwardRuleCache_1141_; lean_object* v_frameBackwardRuleCache_1142_; lean_object* v_frameDB_1143_; lean_object* v_invariants_1144_; lean_object* v_vcs_1145_; lean_object* v_simpState_1146_; lean_object* v_fuel_1147_; lean_object* v_inlineHandledInvariants_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1164_; 
v___x_1138_ = lean_st_ref_take(v_a_1096_);
v_specBackwardRuleCache_1139_ = lean_ctor_get(v___x_1138_, 0);
v_splitBackwardRuleCache_1140_ = lean_ctor_get(v___x_1138_, 1);
v_latticeBackwardRuleCache_1141_ = lean_ctor_get(v___x_1138_, 2);
v_frameBackwardRuleCache_1142_ = lean_ctor_get(v___x_1138_, 3);
v_frameDB_1143_ = lean_ctor_get(v___x_1138_, 4);
v_invariants_1144_ = lean_ctor_get(v___x_1138_, 5);
v_vcs_1145_ = lean_ctor_get(v___x_1138_, 6);
v_simpState_1146_ = lean_ctor_get(v___x_1138_, 7);
v_fuel_1147_ = lean_ctor_get(v___x_1138_, 8);
v_inlineHandledInvariants_1148_ = lean_ctor_get(v___x_1138_, 9);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1150_ = v___x_1138_;
v_isShared_1151_ = v_isSharedCheck_1164_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_inlineHandledInvariants_1148_);
lean_inc(v_fuel_1147_);
lean_inc(v_simpState_1146_);
lean_inc(v_vcs_1145_);
lean_inc(v_invariants_1144_);
lean_inc(v_frameDB_1143_);
lean_inc(v_frameBackwardRuleCache_1142_);
lean_inc(v_latticeBackwardRuleCache_1141_);
lean_inc(v_splitBackwardRuleCache_1140_);
lean_inc(v_specBackwardRuleCache_1139_);
lean_dec(v___x_1138_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1164_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = lean_box(0);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_val_1132_);
v___x_1154_ = v___x_1125_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_toGoalState_1121_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_val_1132_);
v___x_1154_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_array_push(v_vcs_1145_, v___x_1154_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 6, v___x_1155_);
v___x_1157_ = v___x_1150_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_specBackwardRuleCache_1139_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_splitBackwardRuleCache_1140_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_latticeBackwardRuleCache_1141_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_frameBackwardRuleCache_1142_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_frameDB_1143_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_invariants_1144_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_simpState_1146_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_fuel_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_inlineHandledInvariants_1148_);
v___x_1157_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_st_ref_put(v_a_1096_, v___x_1157_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1152_);
v___x_1160_ = v___x_1136_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1152_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1132_);
lean_del_object(v___x_1125_);
lean_dec_ref(v_toGoalState_1121_);
return v___x_1134_;
}
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_dec(v_a_1128_);
lean_del_object(v___x_1125_);
lean_dec_ref(v_toGoalState_1121_);
v___x_1167_ = lean_box(0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1167_);
v___x_1169_ = v___x_1130_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_del_object(v___x_1125_);
lean_dec_ref(v_toGoalState_1121_);
v_a_1172_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1127_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1127_);
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
lean_object* v___x_1182_; lean_object* v___x_1184_; 
lean_dec_ref(v_toGoalState_1121_);
lean_dec(v_a_1117_);
v___x_1182_ = lean_box(0);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1182_);
v___x_1184_ = v___x_1119_;
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
v_a_1187_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1116_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1116_);
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
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1110_);
lean_dec_ref(v_toGoalState_1107_);
v_a_1196_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1112_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1112_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_emitVC_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1094_ = stack[0].m_obj;
lean_object* v_a_1095_ = stack[1].m_obj;
lean_object* v_a_1096_ = stack[2].m_obj;
lean_object* v_a_1097_ = stack[3].m_obj;
lean_object* v_a_1098_ = stack[4].m_obj;
lean_object* v_a_1099_ = stack[5].m_obj;
lean_object* v_a_1100_ = stack[6].m_obj;
lean_object* v_a_1101_ = stack[7].m_obj;
lean_object* v_a_1102_ = stack[8].m_obj;
lean_object* v_a_1103_ = stack[9].m_obj;
lean_object* v_a_1104_ = stack[10].m_obj;
lean_object* v_a_1105_ = stack[11].m_obj;
lean_object* v_res_1205_;
v_res_1205_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
return v_res_1219_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object* v_mvarId_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v_mctx_1224_; lean_object* v_eAssignment_1225_; uint8_t v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1223_ = lean_st_ref_get(v___y_1221_);
v_mctx_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc_ref(v_mctx_1224_);
lean_dec(v___x_1223_);
v_eAssignment_1225_ = lean_ctor_get(v_mctx_1224_, 8);
lean_inc_ref(v_eAssignment_1225_);
lean_dec_ref(v_mctx_1224_);
v___x_1226_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1225_, v_mvarId_1220_);
lean_dec_ref(v_eAssignment_1225_);
v___x_1227_ = lean_box(v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1220_ = stack[0].m_obj;
lean_object* v___y_1221_ = stack[1].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1220_, v___y_1221_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object* v_mvarId_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec(v_mvarId_1230_);
return v_res_1233_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v___x_1234_, lean_object* v_scope_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_bs_1238_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1239_ == 0)
{
lean_dec_ref(v_scope_1235_);
lean_dec_ref(v___x_1234_);
return v_bs_1238_;
}
else
{
lean_object* v_v_1240_; lean_object* v___x_1241_; lean_object* v_bs_x27_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v_v_1240_ = lean_array_uget(v_bs_1238_, v_i_1237_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v_bs_x27_1242_ = lean_array_uset(v_bs_1238_, v_i_1237_, v___x_1241_);
lean_inc_ref(v___x_1234_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1234_);
lean_ctor_set(v___x_1243_, 1, v_v_1240_);
lean_inc_ref(v_scope_1235_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v_scope_1235_);
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1237_, v___x_1245_);
v___x_1247_ = lean_array_uset(v_bs_x27_1242_, v_i_1237_, v___x_1244_);
v_i_1237_ = v___x_1246_;
v_bs_1238_ = v___x_1247_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1234_ = stack[0].m_obj;
lean_object* v_scope_1235_ = stack[1].m_obj;
size_t v_sz_1236_ = stack[2].m_num;
size_t v_i_1237_ = stack[3].m_num;
lean_object* v_bs_1238_ = stack[4].m_obj;
lean_object* v_res_1249_;
v_res_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v___x_1234_, v_scope_1235_, v_sz_1236_, v_i_1237_, v_bs_1238_);
stack->m_obj
 = v_res_1249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v___x_1250_, lean_object* v_scope_1251_, lean_object* v_sz_1252_, lean_object* v_i_1253_, lean_object* v_bs_1254_){
_start:
{
size_t v_sz_boxed_1255_; size_t v_i_boxed_1256_; lean_object* v_res_1257_; 
v_sz_boxed_1255_ = lean_unbox_usize(v_sz_1252_);
lean_dec(v_sz_1252_);
v_i_boxed_1256_ = lean_unbox_usize(v_i_1253_);
lean_dec(v_i_1253_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v___x_1250_, v_scope_1251_, v_sz_boxed_1255_, v_i_boxed_1256_, v_bs_1254_);
return v_res_1257_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_a_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1271_ = lean_array_get_size(v_a_1258_);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_sub(v___x_1271_, v___x_1272_);
v___x_1274_ = lean_nat_dec_lt(v___x_1273_, v___x_1271_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_a_1258_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v_goal_1277_; lean_object* v_scope_1278_; lean_object* v_mvarId_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1276_ = lean_array_fget_borrowed(v_a_1258_, v___x_1273_);
lean_dec(v___x_1273_);
v_goal_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc_ref(v_goal_1277_);
v_scope_1278_ = lean_ctor_get(v___x_1276_, 1);
lean_inc_ref(v_scope_1278_);
v_mvarId_1279_ = lean_ctor_get(v_goal_1277_, 1);
v___x_1280_ = lean_array_pop(v_a_1258_);
v___x_1281_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1279_, v___y_1267_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; uint8_t v___x_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1283_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1277_, v___y_1259_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v_toGoalState_1286_; uint8_t v_inconsistent_1287_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v_toGoalState_1286_ = lean_ctor_get(v_a_1285_, 0);
v_inconsistent_1287_ = lean_ctor_get_uint8(v_toGoalState_1286_, sizeof(void*)*17);
if (v_inconsistent_1287_ == 0)
{
lean_object* v_mvarId_1288_; lean_object* v___x_1289_; 
v_mvarId_1288_ = lean_ctor_get(v_a_1285_, 1);
lean_inc(v_mvarId_1288_);
v___x_1289_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1278_, v_mvarId_1288_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
if (lean_obj_tag(v_a_1290_) == 0)
{
lean_object* v_scope_1291_; lean_object* v_subgoals_1292_; lean_object* v___x_1293_; 
lean_inc_ref(v_toGoalState_1286_);
lean_dec(v_a_1285_);
v_scope_1291_ = lean_ctor_get(v_a_1290_, 0);
lean_inc_ref(v_scope_1291_);
v_subgoals_1292_ = lean_ctor_get(v_a_1290_, 1);
lean_inc(v_subgoals_1292_);
lean_dec_ref_known(v_a_1290_, 2);
v___x_1293_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1292_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v_subgoals_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; size_t v_sz_1296_; size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Array_reverse___redArg(v_a_1294_);
v_sz_1296_ = lean_array_size(v___x_1295_);
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_toGoalState_1286_, v_scope_1291_, v_sz_1296_, v___x_1297_, v___x_1295_);
v___x_1299_ = l_Array_append___redArg(v___x_1280_, v___x_1298_);
lean_dec_ref(v___x_1298_);
v_a_1258_ = v___x_1299_;
goto _start;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_scope_1291_);
lean_dec_ref(v_toGoalState_1286_);
lean_dec_ref(v___x_1280_);
v_a_1301_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1293_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1293_);
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
lean_object* v___x_1309_; 
lean_dec_ref_known(v_a_1290_, 1);
v___x_1309_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1285_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_dec_ref_known(v___x_1309_, 1);
v_a_1258_ = v___x_1280_;
goto _start;
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v___x_1280_);
v_a_1311_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1309_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1285_);
lean_dec_ref(v___x_1280_);
v_a_1319_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1289_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1289_);
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
else
{
lean_dec(v_a_1285_);
lean_dec_ref(v_scope_1278_);
v_a_1258_ = v___x_1280_;
goto _start;
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_scope_1278_);
v_a_1328_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1284_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1284_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_dec_ref(v_scope_1278_);
lean_dec_ref(v_goal_1277_);
v_a_1258_ = v___x_1280_;
goto _start;
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_scope_1278_);
lean_dec_ref(v_goal_1277_);
v_a_1337_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1281_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1281_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1258_ = stack[0].m_obj;
lean_object* v___y_1259_ = stack[1].m_obj;
lean_object* v___y_1260_ = stack[2].m_obj;
lean_object* v___y_1261_ = stack[3].m_obj;
lean_object* v___y_1262_ = stack[4].m_obj;
lean_object* v___y_1263_ = stack[5].m_obj;
lean_object* v___y_1264_ = stack[6].m_obj;
lean_object* v___y_1265_ = stack[7].m_obj;
lean_object* v___y_1266_ = stack[8].m_obj;
lean_object* v___y_1267_ = stack[9].m_obj;
lean_object* v___y_1268_ = stack[10].m_obj;
lean_object* v___y_1269_ = stack[11].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_a_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1359_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1360_, lean_object* v_goal_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_toGoalState_1374_; lean_object* v_mvarId_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1414_; 
v_toGoalState_1374_ = lean_ctor_get(v_goal_1361_, 0);
v_mvarId_1375_ = lean_ctor_get(v_goal_1361_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_goal_1361_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1377_ = v_goal_1361_;
v_isShared_1378_ = v_isSharedCheck_1414_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_mvarId_1375_);
lean_inc(v_toGoalState_1374_);
lean_dec(v_goal_1361_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1414_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1375_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v_a_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_toGoalState_1374_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_a_1380_);
v___x_1382_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_scope_1360_);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_mk_empty_array_with_capacity(v___x_1384_);
v___x_1386_ = lean_array_push(v___x_1385_, v___x_1383_);
v___x_1387_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v___x_1386_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1395_; 
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v___x_1387_, 0);
lean_dec(v_unused_1396_);
v___x_1389_ = v___x_1387_;
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v___x_1387_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1395_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_box(0);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1387_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1387_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1377_);
lean_dec_ref(v_toGoalState_1374_);
lean_dec_ref(v_scope_1360_);
v_a_1406_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1379_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1379_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_work_0interp(lean_interpreter_value* stack)
{
lean_object* v_scope_1360_ = stack[0].m_obj;
lean_object* v_goal_1361_ = stack[1].m_obj;
lean_object* v_a_1362_ = stack[2].m_obj;
lean_object* v_a_1363_ = stack[3].m_obj;
lean_object* v_a_1364_ = stack[4].m_obj;
lean_object* v_a_1365_ = stack[5].m_obj;
lean_object* v_a_1366_ = stack[6].m_obj;
lean_object* v_a_1367_ = stack[7].m_obj;
lean_object* v_a_1368_ = stack[8].m_obj;
lean_object* v_a_1369_ = stack[9].m_obj;
lean_object* v_a_1370_ = stack[10].m_obj;
lean_object* v_a_1371_ = stack[11].m_obj;
lean_object* v_a_1372_ = stack[12].m_obj;
lean_object* v_res_1415_;
v_res_1415_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1360_, v_goal_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
stack->m_obj
 = v_res_1415_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1416_, lean_object* v_goal_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1416_, v_goal_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
return v_res_1430_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v_mvarId_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1431_, v___y_1440_);
return v___x_1444_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1431_ = stack[0].m_obj;
lean_object* v___y_1432_ = stack[1].m_obj;
lean_object* v___y_1433_ = stack[2].m_obj;
lean_object* v___y_1434_ = stack[3].m_obj;
lean_object* v___y_1435_ = stack[4].m_obj;
lean_object* v___y_1436_ = stack[5].m_obj;
lean_object* v___y_1437_ = stack[6].m_obj;
lean_object* v___y_1438_ = stack[7].m_obj;
lean_object* v___y_1439_ = stack[8].m_obj;
lean_object* v___y_1440_ = stack[9].m_obj;
lean_object* v___y_1441_ = stack[10].m_obj;
lean_object* v___y_1442_ = stack[11].m_obj;
lean_object* v_res_1445_;
v_res_1445_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_mvarId_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
stack->m_obj
 = v_res_1445_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v_mvarId_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_mvarId_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v_mvarId_1446_);
return v_res_1459_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_inst_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1461_ = stack[1].m_obj;
lean_object* v___y_1462_ = stack[2].m_obj;
lean_object* v___y_1463_ = stack[3].m_obj;
lean_object* v___y_1464_ = stack[4].m_obj;
lean_object* v___y_1465_ = stack[5].m_obj;
lean_object* v___y_1466_ = stack[6].m_obj;
lean_object* v___y_1467_ = stack[7].m_obj;
lean_object* v___y_1468_ = stack[8].m_obj;
lean_object* v___y_1469_ = stack[9].m_obj;
lean_object* v___y_1470_ = stack[10].m_obj;
lean_object* v___y_1471_ = stack[11].m_obj;
lean_object* v___y_1472_ = stack[12].m_obj;
lean_object* v_res_1475_;
v_res_1475_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_box(0), v_a_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
stack->m_obj
 = v_res_1475_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_inst_1476_, lean_object* v_a_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_inst_1476_, v_a_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1490_;
}
}
lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_config_1502_; lean_object* v_sharedExprs_1503_; uint8_t v_verbose_1504_; uint8_t v_enforceUnfoldReducible_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_config_1502_ = lean_ctor_get(v___y_1495_, 1);
v_sharedExprs_1503_ = lean_ctor_get(v___y_1495_, 0);
v_verbose_1504_ = lean_ctor_get_uint8(v_config_1502_, 0);
v_enforceUnfoldReducible_1505_ = lean_ctor_get_uint8(v_config_1502_, 1);
v___x_1506_ = 0;
v___x_1507_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_1507_, 0, v_verbose_1504_);
lean_ctor_set_uint8(v___x_1507_, 1, v_enforceUnfoldReducible_1505_);
lean_ctor_set_uint8(v___x_1507_, 2, v___x_1506_);
lean_inc_ref(v_sharedExprs_1503_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_sharedExprs_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
v___x_1509_ = lean_apply_10(v_x_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___x_1508_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, lean_box(0));
return v___x_1509_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1491_ = stack[0].m_obj;
lean_object* v___y_1492_ = stack[1].m_obj;
lean_object* v___y_1493_ = stack[2].m_obj;
lean_object* v___y_1494_ = stack[3].m_obj;
lean_object* v___y_1495_ = stack[4].m_obj;
lean_object* v___y_1496_ = stack[5].m_obj;
lean_object* v___y_1497_ = stack[6].m_obj;
lean_object* v___y_1498_ = stack[7].m_obj;
lean_object* v___y_1499_ = stack[8].m_obj;
lean_object* v___y_1500_ = stack[9].m_obj;
lean_object* v_res_1510_;
v_res_1510_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
stack->m_obj
 = v_res_1510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
return v_res_1522_;
}
}
lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_1523_, lean_object* v_x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1524_ = stack[1].m_obj;
lean_object* v___y_1525_ = stack[2].m_obj;
lean_object* v___y_1526_ = stack[3].m_obj;
lean_object* v___y_1527_ = stack[4].m_obj;
lean_object* v___y_1528_ = stack[5].m_obj;
lean_object* v___y_1529_ = stack[6].m_obj;
lean_object* v___y_1530_ = stack[7].m_obj;
lean_object* v___y_1531_ = stack[8].m_obj;
lean_object* v___y_1532_ = stack[9].m_obj;
lean_object* v___y_1533_ = stack[10].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_box(0), v_x_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_x_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_1537_, v_x_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
return v_res_1549_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_1550_, lean_object* v_scope_1551_, lean_object* v_goal_1552_, lean_object* v_ctx_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_st_mk_ref(v_initState_1550_);
v___x_1565_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1551_, v_goal_1552_, v_ctx_1553_, v___x_1564_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1575_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1575_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1575_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_st_ref_get(v___x_1564_);
lean_dec(v___x_1564_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1566_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v___x_1564_);
v_a_1576_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1565_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1565_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_run___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_initState_1550_ = stack[0].m_obj;
lean_object* v_scope_1551_ = stack[1].m_obj;
lean_object* v_goal_1552_ = stack[2].m_obj;
lean_object* v_ctx_1553_ = stack[3].m_obj;
lean_object* v___y_1554_ = stack[4].m_obj;
lean_object* v___y_1555_ = stack[5].m_obj;
lean_object* v___y_1556_ = stack[6].m_obj;
lean_object* v___y_1557_ = stack[7].m_obj;
lean_object* v___y_1558_ = stack[8].m_obj;
lean_object* v___y_1559_ = stack[9].m_obj;
lean_object* v___y_1560_ = stack[10].m_obj;
lean_object* v___y_1561_ = stack[11].m_obj;
lean_object* v___y_1562_ = stack[12].m_obj;
lean_object* v_res_1584_;
v_res_1584_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_1550_, v_scope_1551_, v_goal_1552_, v_ctx_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
stack->m_obj
 = v_res_1584_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_1585_, lean_object* v_scope_1586_, lean_object* v_goal_1587_, lean_object* v_ctx_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_1585_, v_scope_1586_, v_goal_1587_, v_ctx_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v_ctx_1588_);
return v_res_1599_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v_mctx_1604_; lean_object* v_eAssignment_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1603_ = lean_st_ref_get(v___y_1601_);
v_mctx_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc_ref(v_mctx_1604_);
lean_dec(v___x_1603_);
v_eAssignment_1605_ = lean_ctor_get(v_mctx_1604_, 8);
lean_inc_ref(v_eAssignment_1605_);
lean_dec_ref(v_mctx_1604_);
v___x_1606_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1605_, v_mvarId_1600_);
lean_dec_ref(v_eAssignment_1605_);
v___x_1607_ = lean_box(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1600_ = stack[0].m_obj;
lean_object* v___y_1601_ = stack[1].m_obj;
lean_object* v_res_1609_;
v_res_1609_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1600_, v___y_1601_);
stack->m_obj
 = v_res_1609_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec(v_mvarId_1610_);
return v_res_1613_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_1614_, size_t v_i_1615_, size_t v_stop_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_a_1629_; uint8_t v___x_1633_; 
v___x_1633_ = lean_usize_dec_eq(v_i_1615_, v_stop_1616_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v_mvarId_1637_; lean_object* v___x_1638_; 
v___x_1634_ = lean_array_uget_borrowed(v_as_1614_, v_i_1615_);
v_mvarId_1637_ = lean_ctor_get(v___x_1634_, 1);
v___x_1638_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1637_, v___y_1624_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; uint8_t v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = lean_unbox(v_a_1639_);
lean_dec(v_a_1639_);
if (v___x_1640_ == 0)
{
goto v___jp_1635_;
}
else
{
v_a_1629_ = v_b_1617_;
goto v___jp_1628_;
}
}
else
{
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1641_; uint8_t v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1642_ = lean_unbox(v_a_1641_);
lean_dec(v_a_1641_);
if (v___x_1642_ == 0)
{
v_a_1629_ = v_b_1617_;
goto v___jp_1628_;
}
else
{
goto v___jp_1635_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_b_1617_);
v_a_1643_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1638_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1638_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1636_; 
lean_inc(v___x_1634_);
v___x_1636_ = lean_array_push(v_b_1617_, v___x_1634_);
v_a_1629_ = v___x_1636_;
goto v___jp_1628_;
}
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_b_1617_);
return v___x_1651_;
}
v___jp_1628_:
{
size_t v___x_1630_; size_t v___x_1631_; 
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = lean_usize_add(v_i_1615_, v___x_1630_);
v_i_1615_ = v___x_1631_;
v_b_1617_ = v_a_1629_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1614_ = stack[0].m_obj;
size_t v_i_1615_ = stack[1].m_num;
size_t v_stop_1616_ = stack[2].m_num;
lean_object* v_b_1617_ = stack[3].m_obj;
lean_object* v___y_1618_ = stack[4].m_obj;
lean_object* v___y_1619_ = stack[5].m_obj;
lean_object* v___y_1620_ = stack[6].m_obj;
lean_object* v___y_1621_ = stack[7].m_obj;
lean_object* v___y_1622_ = stack[8].m_obj;
lean_object* v___y_1623_ = stack[9].m_obj;
lean_object* v___y_1624_ = stack[10].m_obj;
lean_object* v___y_1625_ = stack[11].m_obj;
lean_object* v___y_1626_ = stack[12].m_obj;
lean_object* v_res_1652_;
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_1614_, v_i_1615_, v_stop_1616_, v_b_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_1653_, lean_object* v_i_1654_, lean_object* v_stop_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
size_t v_i_boxed_1667_; size_t v_stop_boxed_1668_; lean_object* v_res_1669_; 
v_i_boxed_1667_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_stop_boxed_1668_ = lean_unbox_usize(v_stop_1655_);
lean_dec(v_stop_1655_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_1653_, v_i_boxed_1667_, v_stop_boxed_1668_, v_b_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_1671_, size_t v_i_1672_, lean_object* v_bs_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_bs_1673_);
return v___x_1680_;
}
else
{
lean_object* v_v_1681_; lean_object* v_mvarId_1682_; lean_object* v___x_1683_; lean_object* v_bs_x27_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_v_1681_ = lean_array_uget_borrowed(v_bs_1673_, v_i_1672_);
v_mvarId_1682_ = lean_ctor_get(v_v_1681_, 1);
lean_inc_n(v_mvarId_1682_, 2);
v___x_1683_ = lean_unsigned_to_nat(0u);
v_bs_x27_1684_ = lean_array_uset(v_bs_1673_, v_i_1672_, v___x_1683_);
v___x_1685_ = lean_usize_to_nat(v_i_1672_);
v___x_1686_ = l_Lean_MVarId_getTag(v_mvarId_1682_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_add(v___x_1685_, v___x_1689_);
lean_dec(v___x_1685_);
v___x_1691_ = l_Nat_reprFast(v___x_1690_);
v___x_1692_ = lean_string_append(v___x_1688_, v___x_1691_);
lean_dec_ref(v___x_1691_);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Lean_Name_str___override(v___x_1693_, v___x_1692_);
v___x_1695_ = l_Lean_Name_eraseMacroScopes(v_a_1687_);
lean_dec(v_a_1687_);
v___x_1696_ = l_Lean_Name_append(v___x_1694_, v___x_1695_);
v___x_1697_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1682_, v___x_1696_, v___y_1675_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; size_t v___x_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_add(v_i_1672_, v___x_1699_);
v___x_1701_ = lean_array_uset(v_bs_x27_1684_, v_i_1672_, v_a_1698_);
v_i_1672_ = v___x_1700_;
v_bs_1673_ = v___x_1701_;
goto _start;
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v_bs_x27_1684_);
v_a_1703_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1697_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1697_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v___x_1685_);
lean_dec_ref(v_bs_x27_1684_);
lean_dec(v_mvarId_1682_);
v_a_1711_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1686_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1686_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1671_ = stack[0].m_num;
size_t v_i_1672_ = stack[1].m_num;
lean_object* v_bs_1673_ = stack[2].m_obj;
lean_object* v___y_1674_ = stack[3].m_obj;
lean_object* v___y_1675_ = stack[4].m_obj;
lean_object* v___y_1676_ = stack[5].m_obj;
lean_object* v___y_1677_ = stack[6].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1671_, v_i_1672_, v_bs_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_bs_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
size_t v_sz_boxed_1728_; size_t v_i_boxed_1729_; lean_object* v_res_1730_; 
v_sz_boxed_1728_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1729_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_1728_, v_i_boxed_1729_, v_bs_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1730_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_1732_, size_t v_i_1733_, lean_object* v_bs_1734_, lean_object* v___y_1735_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_lt(v_i_1733_, v_sz_1732_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_bs_1734_);
return v___x_1738_;
}
else
{
lean_object* v_v_1739_; lean_object* v___x_1740_; lean_object* v_bs_x27_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_v_1739_ = lean_array_uget(v_bs_1734_, v_i_1733_);
v___x_1740_ = lean_unsigned_to_nat(0u);
v_bs_x27_1741_ = lean_array_uset(v_bs_1734_, v_i_1733_, v___x_1740_);
v___x_1742_ = lean_usize_to_nat(v_i_1733_);
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = lean_nat_add(v___x_1742_, v___x_1744_);
lean_dec(v___x_1742_);
v___x_1746_ = l_Nat_reprFast(v___x_1745_);
v___x_1747_ = lean_string_append(v___x_1743_, v___x_1746_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_box(0);
v___x_1749_ = l_Lean_Name_str___override(v___x_1748_, v___x_1747_);
v___x_1750_ = l_Lean_MVarId_setTag___redArg(v_v_1739_, v___x_1749_, v___y_1735_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1733_, v___x_1752_);
v___x_1754_ = lean_array_uset(v_bs_x27_1741_, v_i_1733_, v_a_1751_);
v_i_1733_ = v___x_1753_;
v_bs_1734_ = v___x_1754_;
goto _start;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v_bs_x27_1741_);
v_a_1756_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1750_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1750_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1732_ = stack[0].m_num;
size_t v_i_1733_ = stack[1].m_num;
lean_object* v_bs_1734_ = stack[2].m_obj;
lean_object* v___y_1735_ = stack[3].m_obj;
lean_object* v_res_1764_;
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1732_, v_i_1733_, v_bs_1734_, v___y_1735_);
stack->m_obj
 = v_res_1764_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1765_, lean_object* v_i_1766_, lean_object* v_bs_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1765_);
lean_dec(v_sz_1765_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1766_);
lean_dec(v_i_1766_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_1770_, v_i_boxed_1771_, v_bs_1767_, v___y_1768_);
lean_dec(v___y_1768_);
return v_res_1772_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_1773_, size_t v_i_1774_, size_t v_stop_1775_, lean_object* v_b_1776_){
_start:
{
lean_object* v___y_1778_; uint8_t v___x_1782_; 
v___x_1782_ = lean_usize_dec_eq(v_i_1774_, v_stop_1775_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; uint8_t v_retired_1784_; 
v___x_1783_ = lean_array_uget_borrowed(v_as_1773_, v_i_1774_);
v_retired_1784_ = lean_ctor_get_uint8(v___x_1783_, sizeof(void*)*4);
if (v_retired_1784_ == 0)
{
lean_object* v_frameStx_1785_; lean_object* v___x_1786_; 
v_frameStx_1785_ = lean_ctor_get(v___x_1783_, 2);
lean_inc(v_frameStx_1785_);
v___x_1786_ = lean_array_push(v_b_1776_, v_frameStx_1785_);
v___y_1778_ = v___x_1786_;
goto v___jp_1777_;
}
else
{
v___y_1778_ = v_b_1776_;
goto v___jp_1777_;
}
}
else
{
return v_b_1776_;
}
v___jp_1777_:
{
size_t v___x_1779_; size_t v___x_1780_; 
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1774_, v___x_1779_);
v_i_1774_ = v___x_1780_;
v_b_1776_ = v___y_1778_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1773_ = stack[0].m_obj;
size_t v_i_1774_ = stack[1].m_num;
size_t v_stop_1775_ = stack[2].m_num;
lean_object* v_b_1776_ = stack[3].m_obj;
lean_object* v_res_1787_;
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1773_, v_i_1774_, v_stop_1775_, v_b_1776_);
stack->m_obj
 = v_res_1787_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_1788_, lean_object* v_i_1789_, lean_object* v_stop_1790_, lean_object* v_b_1791_){
_start:
{
size_t v_i_boxed_1792_; size_t v_stop_boxed_1793_; lean_object* v_res_1794_; 
v_i_boxed_1792_ = lean_unbox_usize(v_i_1789_);
lean_dec(v_i_1789_);
v_stop_boxed_1793_ = lean_unbox_usize(v_stop_1790_);
lean_dec(v_stop_1790_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1788_, v_i_boxed_1792_, v_stop_boxed_1793_, v_b_1791_);
lean_dec_ref(v_as_1788_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_1797_, lean_object* v_start_1798_, lean_object* v_stop_1799_){
_start:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0));
v___x_1801_ = lean_nat_dec_lt(v_start_1798_, v_stop_1799_);
if (v___x_1801_ == 0)
{
return v___x_1800_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = lean_array_get_size(v_as_1797_);
v___x_1803_ = lean_nat_dec_le(v_stop_1799_, v___x_1802_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_nat_dec_lt(v_start_1798_, v___x_1802_);
if (v___x_1804_ == 0)
{
return v___x_1800_;
}
else
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_usize_of_nat(v_start_1798_);
v___x_1806_ = lean_usize_of_nat(v___x_1802_);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1797_, v___x_1805_, v___x_1806_, v___x_1800_);
return v___x_1807_;
}
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_usize_of_nat(v_start_1798_);
v___x_1809_ = lean_usize_of_nat(v_stop_1799_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_1797_, v___x_1808_, v___x_1809_, v___x_1800_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_1811_, lean_object* v_start_1812_, lean_object* v_stop_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_1811_, v_start_1812_, v_stop_1813_);
lean_dec(v_stop_1813_);
lean_dec(v_start_1812_);
lean_dec_ref(v_as_1811_);
return v_res_1814_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_unsigned_to_nat(16u);
v___x_1817_ = lean_mk_array(v___x_1816_, v___x_1815_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
lean_ctor_set(v___x_1826_, 2, v___x_1824_);
lean_ctor_set(v___x_1826_, 3, v___x_1824_);
return v___x_1826_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_1827_, lean_object* v_ctx_1828_, lean_object* v_scope_1829_, lean_object* v_stepLimit_x3f_1830_, lean_object* v_frameDB_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v_a_1847_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___y_1871_; 
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1869_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_1830_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(1);
v___y_1871_ = v___x_1917_;
goto v___jp_1870_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_val_1918_ = lean_ctor_get(v_stepLimit_x3f_1830_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_stepLimit_x3f_1830_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v_stepLimit_x3f_1830_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_val_1918_);
lean_dec(v_stepLimit_x3f_1830_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 0);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_val_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
v___y_1871_ = v___x_1923_;
goto v___jp_1870_;
}
}
}
v___jp_1843_:
{
lean_object* v_entries_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_entries_1848_ = lean_ctor_get(v___y_1845_, 1);
lean_inc_ref(v_entries_1848_);
lean_dec_ref(v___y_1845_);
v___x_1849_ = lean_array_get_size(v_entries_1848_);
v___x_1850_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_1848_, v___x_1842_, v___x_1849_);
lean_dec_ref(v_entries_1848_);
v___x_1851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1851_, 0, v___y_1846_);
lean_ctor_set(v___x_1851_, 1, v_a_1847_);
lean_ctor_set(v___x_1851_, 2, v___y_1844_);
lean_ctor_set(v___x_1851_, 3, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
v___jp_1853_:
{
if (lean_obj_tag(v___y_1857_) == 0)
{
lean_object* v_a_1858_; 
v_a_1858_ = lean_ctor_get(v___y_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___y_1857_, 1);
v___y_1844_ = v___y_1854_;
v___y_1845_ = v___y_1855_;
v___y_1846_ = v___y_1856_;
v_a_1847_ = v_a_1858_;
goto v___jp_1843_;
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec_ref(v___y_1854_);
v_a_1859_ = lean_ctor_get(v___y_1857_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___y_1857_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___y_1857_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___y_1857_);
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
v___jp_1870_:
{
lean_object* v_initState_1872_; lean_object* v___f_1873_; lean_object* v___x_1874_; 
v_initState_1872_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_initState_1872_, 0, v___x_1867_);
lean_ctor_set(v_initState_1872_, 1, v___x_1867_);
lean_ctor_set(v_initState_1872_, 2, v___x_1867_);
lean_ctor_set(v_initState_1872_, 3, v___x_1867_);
lean_ctor_set(v_initState_1872_, 4, v_frameDB_1831_);
lean_ctor_set(v_initState_1872_, 5, v___x_1868_);
lean_ctor_set(v_initState_1872_, 6, v___x_1868_);
lean_ctor_set(v_initState_1872_, 7, v___x_1869_);
lean_ctor_set(v_initState_1872_, 8, v___y_1871_);
lean_ctor_set(v_initState_1872_, 9, v___x_1867_);
v___f_1873_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_1873_, 0, v_initState_1872_);
lean_closure_set(v___f_1873_, 1, v_scope_1829_);
lean_closure_set(v___f_1873_, 2, v_goal_1827_);
lean_closure_set(v___f_1873_, 3, v_ctx_1828_);
v___x_1874_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_1873_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_snd_1876_; lean_object* v_frameDB_1877_; lean_object* v_invariants_1878_; lean_object* v_vcs_1879_; lean_object* v_inlineHandledInvariants_1880_; size_t v_sz_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v_snd_1876_ = lean_ctor_get(v_a_1875_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_a_1875_);
v_frameDB_1877_ = lean_ctor_get(v_snd_1876_, 4);
lean_inc_ref(v_frameDB_1877_);
v_invariants_1878_ = lean_ctor_get(v_snd_1876_, 5);
lean_inc_ref_n(v_invariants_1878_, 2);
v_vcs_1879_ = lean_ctor_get(v_snd_1876_, 6);
lean_inc_ref(v_vcs_1879_);
v_inlineHandledInvariants_1880_ = lean_ctor_get(v_snd_1876_, 9);
lean_inc_ref(v_inlineHandledInvariants_1880_);
lean_dec(v_snd_1876_);
v_sz_1881_ = lean_array_size(v_invariants_1878_);
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1881_, v___x_1882_, v_invariants_1878_, v_a_1838_);
if (lean_obj_tag(v___x_1883_) == 0)
{
size_t v_sz_1884_; lean_object* v___x_1885_; 
lean_dec_ref_known(v___x_1883_, 1);
v_sz_1884_ = lean_array_size(v_vcs_1879_);
lean_inc_ref(v_vcs_1879_);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_1884_, v___x_1882_, v_vcs_1879_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
lean_dec_ref_known(v___x_1885_, 1);
v___x_1886_ = lean_array_get_size(v_vcs_1879_);
v___x_1887_ = lean_nat_dec_lt(v___x_1842_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_dec_ref(v_vcs_1879_);
v___y_1844_ = v_inlineHandledInvariants_1880_;
v___y_1845_ = v_frameDB_1877_;
v___y_1846_ = v_invariants_1878_;
v_a_1847_ = v___x_1868_;
goto v___jp_1843_;
}
else
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_le(v___x_1886_, v___x_1886_);
if (v___x_1888_ == 0)
{
if (v___x_1887_ == 0)
{
lean_dec_ref(v_vcs_1879_);
v___y_1844_ = v_inlineHandledInvariants_1880_;
v___y_1845_ = v_frameDB_1877_;
v___y_1846_ = v_invariants_1878_;
v_a_1847_ = v___x_1868_;
goto v___jp_1843_;
}
else
{
size_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_usize_of_nat(v___x_1886_);
v___x_1890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1879_, v___x_1882_, v___x_1889_, v___x_1868_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec_ref(v_vcs_1879_);
v___y_1854_ = v_inlineHandledInvariants_1880_;
v___y_1855_ = v_frameDB_1877_;
v___y_1856_ = v_invariants_1878_;
v___y_1857_ = v___x_1890_;
goto v___jp_1853_;
}
}
else
{
size_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_usize_of_nat(v___x_1886_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_1879_, v___x_1882_, v___x_1891_, v___x_1868_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec_ref(v_vcs_1879_);
v___y_1854_ = v_inlineHandledInvariants_1880_;
v___y_1855_ = v_frameDB_1877_;
v___y_1856_ = v_invariants_1878_;
v___y_1857_ = v___x_1892_;
goto v___jp_1853_;
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_inlineHandledInvariants_1880_);
lean_dec_ref(v_vcs_1879_);
lean_dec_ref(v_invariants_1878_);
lean_dec_ref(v_frameDB_1877_);
v_a_1893_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1885_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1885_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v_inlineHandledInvariants_1880_);
lean_dec_ref(v_vcs_1879_);
lean_dec_ref(v_invariants_1878_);
lean_dec_ref(v_frameDB_1877_);
v_a_1901_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1883_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1883_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1874_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1874_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_1827_ = stack[0].m_obj;
lean_object* v_ctx_1828_ = stack[1].m_obj;
lean_object* v_scope_1829_ = stack[2].m_obj;
lean_object* v_stepLimit_x3f_1830_ = stack[3].m_obj;
lean_object* v_frameDB_1831_ = stack[4].m_obj;
lean_object* v_a_1832_ = stack[5].m_obj;
lean_object* v_a_1833_ = stack[6].m_obj;
lean_object* v_a_1834_ = stack[7].m_obj;
lean_object* v_a_1835_ = stack[8].m_obj;
lean_object* v_a_1836_ = stack[9].m_obj;
lean_object* v_a_1837_ = stack[10].m_obj;
lean_object* v_a_1838_ = stack[11].m_obj;
lean_object* v_a_1839_ = stack[12].m_obj;
lean_object* v_a_1840_ = stack[13].m_obj;
lean_object* v_res_1926_;
v_res_1926_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_1827_, v_ctx_1828_, v_scope_1829_, v_stepLimit_x3f_1830_, v_frameDB_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_1927_, lean_object* v_ctx_1928_, lean_object* v_scope_1929_, lean_object* v_stepLimit_x3f_1930_, lean_object* v_frameDB_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_1927_, v_ctx_1928_, v_scope_1929_, v_stepLimit_x3f_1930_, v_frameDB_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1940_);
lean_dec_ref(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
return v_res_1942_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1943_, v___y_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1943_ = stack[0].m_obj;
lean_object* v___y_1944_ = stack[1].m_obj;
lean_object* v___y_1945_ = stack[2].m_obj;
lean_object* v___y_1946_ = stack[3].m_obj;
lean_object* v___y_1947_ = stack[4].m_obj;
lean_object* v___y_1948_ = stack[5].m_obj;
lean_object* v___y_1949_ = stack[6].m_obj;
lean_object* v___y_1950_ = stack[7].m_obj;
lean_object* v___y_1951_ = stack[8].m_obj;
lean_object* v___y_1952_ = stack[9].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
stack->m_obj
 = v_res_1955_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v_mvarId_1956_);
return v_res_1967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_1968_, size_t v_sz_1969_, size_t v_i_1970_, lean_object* v_bs_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_1969_, v_i_1970_, v_bs_1971_, v___y_1978_);
return v___x_1982_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1968_ = stack[0].m_obj;
size_t v_sz_1969_ = stack[1].m_num;
size_t v_i_1970_ = stack[2].m_num;
lean_object* v_bs_1971_ = stack[3].m_obj;
lean_object* v___y_1972_ = stack[4].m_obj;
lean_object* v___y_1973_ = stack[5].m_obj;
lean_object* v___y_1974_ = stack[6].m_obj;
lean_object* v___y_1975_ = stack[7].m_obj;
lean_object* v___y_1976_ = stack[8].m_obj;
lean_object* v___y_1977_ = stack[9].m_obj;
lean_object* v___y_1978_ = stack[10].m_obj;
lean_object* v___y_1979_ = stack[11].m_obj;
lean_object* v___y_1980_ = stack[12].m_obj;
lean_object* v_res_1983_;
v_res_1983_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_1968_, v_sz_1969_, v_i_1970_, v_bs_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
stack->m_obj
 = v_res_1983_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_1984_, lean_object* v_sz_1985_, lean_object* v_i_1986_, lean_object* v_bs_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
size_t v_sz_boxed_1998_; size_t v_i_boxed_1999_; lean_object* v_res_2000_; 
v_sz_boxed_1998_ = lean_unbox_usize(v_sz_1985_);
lean_dec(v_sz_1985_);
v_i_boxed_1999_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_1984_, v_sz_boxed_1998_, v_i_boxed_1999_, v_bs_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v_as_1984_);
return v_res_2000_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_2001_, size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_bs_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2002_, v_i_2003_, v_bs_2004_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2001_ = stack[0].m_obj;
size_t v_sz_2002_ = stack[1].m_num;
size_t v_i_2003_ = stack[2].m_num;
lean_object* v_bs_2004_ = stack[3].m_obj;
lean_object* v___y_2005_ = stack[4].m_obj;
lean_object* v___y_2006_ = stack[5].m_obj;
lean_object* v___y_2007_ = stack[6].m_obj;
lean_object* v___y_2008_ = stack[7].m_obj;
lean_object* v___y_2009_ = stack[8].m_obj;
lean_object* v___y_2010_ = stack[9].m_obj;
lean_object* v___y_2011_ = stack[10].m_obj;
lean_object* v___y_2012_ = stack[11].m_obj;
lean_object* v___y_2013_ = stack[12].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_2001_, v_sz_2002_, v_i_2003_, v_bs_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_2017_, lean_object* v_sz_2018_, lean_object* v_i_2019_, lean_object* v_bs_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
size_t v_sz_boxed_2031_; size_t v_i_boxed_2032_; lean_object* v_res_2033_; 
v_sz_boxed_2031_ = lean_unbox_usize(v_sz_2018_);
lean_dec(v_sz_2018_);
v_i_boxed_2032_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_2017_, v_sz_boxed_2031_, v_i_boxed_2032_, v_bs_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v_as_2017_);
return v_res_2033_;
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
