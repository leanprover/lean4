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
lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
size_t v_x_14584__boxed_174_; size_t v_x_14585__boxed_175_; lean_object* v_res_176_; 
v_x_14584__boxed_174_ = lean_unbox_usize(v_x_170_);
lean_dec(v_x_170_);
v_x_14585__boxed_175_ = lean_unbox_usize(v_x_171_);
lean_dec(v_x_171_);
v_res_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_169_, v_x_14584__boxed_174_, v_x_14585__boxed_175_, v_x_172_, v_x_173_);
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
size_t v_x_14806__boxed_266_; uint8_t v_res_267_; lean_object* v_r_268_; 
v_x_14806__boxed_266_ = lean_unbox_usize(v_x_264_);
lean_dec(v_x_264_);
v_res_267_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_263_, v_x_14806__boxed_266_, v_x_265_);
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
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___y_322_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_toCold_368_; lean_object* v_currRecDepth_369_; lean_object* v_ref_370_; uint16_t v_optionFlags_371_; uint8_t v_suppressElabErrors_372_; uint8_t v_checkDeprecated_373_; uint8_t v_isRecordingDeps_374_; lean_object* v___x_375_; uint8_t v_transparency_376_; lean_object* v___x_377_; uint8_t v___x_378_; lean_object* v_ref_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_313_ = lean_box(0);
v___x_314_ = lean_box(0);
v___x_315_ = 1;
v___x_319_ = lean_box(1);
v___x_320_ = 0;
v___x_366_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__2));
v___x_367_ = lean_alloc_ctor(0, 8, 10);
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
v_toCold_368_ = lean_ctor_get(v___y_310_, 0);
v_currRecDepth_369_ = lean_ctor_get(v___y_310_, 1);
v_ref_370_ = lean_ctor_get(v___y_310_, 2);
v_optionFlags_371_ = lean_ctor_get_uint16(v___y_310_, sizeof(void*)*3);
v_suppressElabErrors_372_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*3 + 2);
v_checkDeprecated_373_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*3 + 3);
v_isRecordingDeps_374_ = lean_ctor_get_uint8(v___y_310_, sizeof(void*)*3 + 4);
v___x_375_ = l_Lean_Meta_Context_config(v___y_308_);
v_transparency_376_ = lean_ctor_get_uint8(v___x_375_, 9);
lean_dec_ref(v___x_375_);
v___x_377_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___closed__3));
v___x_378_ = 1;
v_ref_379_ = l_Lean_replaceRef(v_val_304_, v_ref_370_);
lean_inc(v_currRecDepth_369_);
lean_inc_ref(v_toCold_368_);
v___x_380_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_380_, 0, v_toCold_368_);
lean_ctor_set(v___x_380_, 1, v_currRecDepth_369_);
lean_ctor_set(v___x_380_, 2, v_ref_379_);
lean_ctor_set_uint16(v___x_380_, sizeof(void*)*3, v_optionFlags_371_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 2, v_suppressElabErrors_372_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 3, v_checkDeprecated_373_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*3 + 4, v_isRecordingDeps_374_);
v___x_381_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_376_, v___x_378_);
if (v___x_381_ == 0)
{
lean_object* v_keyedConfig_382_; uint8_t v_trackZetaDelta_383_; lean_object* v_zetaDeltaSet_384_; lean_object* v_lctx_385_; lean_object* v_localInstances_386_; lean_object* v_defEqCtx_x3f_387_; lean_object* v_synthPendingDepth_388_; lean_object* v_customCanUnfoldPredicate_x3f_389_; uint8_t v_univApprox_390_; uint8_t v_inTypeClassResolution_391_; uint8_t v_cacheInferType_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_keyedConfig_382_ = lean_ctor_get(v___y_308_, 0);
v_trackZetaDelta_383_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7);
v_zetaDeltaSet_384_ = lean_ctor_get(v___y_308_, 1);
v_lctx_385_ = lean_ctor_get(v___y_308_, 2);
v_localInstances_386_ = lean_ctor_get(v___y_308_, 3);
v_defEqCtx_x3f_387_ = lean_ctor_get(v___y_308_, 4);
v_synthPendingDepth_388_ = lean_ctor_get(v___y_308_, 5);
v_customCanUnfoldPredicate_x3f_389_ = lean_ctor_get(v___y_308_, 6);
v_univApprox_390_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_391_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 2);
v_cacheInferType_392_ = lean_ctor_get_uint8(v___y_308_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_382_);
v___x_393_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_378_, v_keyedConfig_382_);
lean_inc(v_customCanUnfoldPredicate_x3f_389_);
lean_inc(v_synthPendingDepth_388_);
lean_inc(v_defEqCtx_x3f_387_);
lean_inc_ref(v_localInstances_386_);
lean_inc_ref(v_lctx_385_);
lean_inc(v_zetaDeltaSet_384_);
v___x_394_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_zetaDeltaSet_384_);
lean_ctor_set(v___x_394_, 2, v_lctx_385_);
lean_ctor_set(v___x_394_, 3, v_localInstances_386_);
lean_ctor_set(v___x_394_, 4, v_defEqCtx_x3f_387_);
lean_ctor_set(v___x_394_, 5, v_synthPendingDepth_388_);
lean_ctor_set(v___x_394_, 6, v_customCanUnfoldPredicate_x3f_389_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*7, v_trackZetaDelta_383_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*7 + 1, v_univApprox_390_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*7 + 2, v_inTypeClassResolution_391_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*7 + 3, v_cacheInferType_392_);
lean_inc(v_mv_303_);
v___x_395_ = l_Lean_Elab_runTactic(v_mv_303_, v_tac_305_, v___x_367_, v___x_377_, v___x_394_, v___y_309_, v___x_380_, v___y_311_);
lean_dec_ref_known(v___x_380_, 3);
lean_dec_ref_known(v___x_394_, 7);
v___y_322_ = v___x_395_;
goto v___jp_321_;
}
else
{
lean_object* v___x_396_; 
lean_inc(v_mv_303_);
v___x_396_ = l_Lean_Elab_runTactic(v_mv_303_, v_tac_305_, v___x_367_, v___x_377_, v___y_308_, v___y_309_, v___x_380_, v___y_311_);
lean_dec_ref_known(v___x_380_, 3);
v___y_322_ = v___x_396_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_397_, lean_object* v_mv_398_, lean_object* v_val_399_, lean_object* v_tac_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_397_, v_mv_398_, v_val_399_, v_tac_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v_val_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
else
{
lean_object* v_key_412_; lean_object* v_value_413_; lean_object* v_tail_414_; uint8_t v___x_415_; 
v_key_412_ = lean_ctor_get(v_x_410_, 0);
v_value_413_ = lean_ctor_get(v_x_410_, 1);
v_tail_414_ = lean_ctor_get(v_x_410_, 2);
v___x_415_ = lean_nat_dec_eq(v_key_412_, v_a_409_);
if (v___x_415_ == 0)
{
v_x_410_ = v_tail_414_;
goto _start;
}
else
{
lean_object* v___x_417_; 
lean_inc(v_value_413_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_value_413_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_418_, v_x_419_);
lean_dec(v_x_419_);
lean_dec(v_a_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_buckets_423_; lean_object* v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v_fold_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_buckets_423_ = lean_ctor_get(v_m_421_, 1);
v___x_424_ = lean_array_get_size(v_buckets_423_);
v___x_425_ = lean_uint64_of_nat(v_a_422_);
v___x_426_ = 32ULL;
v___x_427_ = lean_uint64_shift_right(v___x_425_, v___x_426_);
v_fold_428_ = lean_uint64_xor(v___x_425_, v___x_427_);
v___x_429_ = 16ULL;
v___x_430_ = lean_uint64_shift_right(v_fold_428_, v___x_429_);
v___x_431_ = lean_uint64_xor(v_fold_428_, v___x_430_);
v___x_432_ = lean_uint64_to_usize(v___x_431_);
v___x_433_ = lean_usize_of_nat(v___x_424_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_sub(v___x_433_, v___x_434_);
v___x_436_ = lean_usize_land(v___x_432_, v___x_435_);
v___x_437_ = lean_array_uget_borrowed(v_buckets_423_, v___x_436_);
v___x_438_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_422_, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_m_439_);
return v_res_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22(void){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Array_mkArray0___redArg();
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object* v_invariantAlts_506_, lean_object* v_n_507_, lean_object* v_mv_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___y_517_; lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_506_, v_n_507_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_616_; 
v_val_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_616_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_616_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_616_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___f_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___f_549_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0));
v___x_550_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5));
lean_inc(v_val_545_);
v___x_551_ = l_Lean_Syntax_isOfKind(v_val_545_, v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7));
lean_inc(v_val_545_);
v___x_553_ = l_Lean_Syntax_isOfKind(v_val_545_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_556_; 
lean_dec(v_val_545_);
lean_dec(v_mv_508_);
v___x_554_ = lean_box(v___x_553_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
lean_ctor_set(v___x_547_, 0, v___x_554_);
v___x_556_ = v___x_547_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = l_Lean_Syntax_getArg(v_val_545_, v___x_558_);
v___x_560_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9));
lean_inc(v___x_559_);
v___x_561_ = l_Lean_Syntax_isOfKind(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec(v___x_559_);
lean_dec(v_val_545_);
lean_dec(v_mv_508_);
v___x_562_ = lean_box(v___x_561_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
lean_ctor_set(v___x_547_, 0, v___x_562_);
v___x_564_ = v___x_547_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v_ref_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_args_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_547_);
v_ref_566_ = lean_ctor_get(v_a_513_, 2);
v___x_567_ = l_Lean_Syntax_getArg(v___x_559_, v___x_558_);
lean_dec(v___x_559_);
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = l_Lean_Syntax_getArg(v_val_545_, v___x_568_);
v_args_570_ = l_Lean_Syntax_getArgs(v___x_567_);
lean_dec(v___x_567_);
v___x_571_ = l_Lean_SourceInfo_fromRef(v_ref_566_, v___x_551_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__11));
v___x_573_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__12));
lean_inc_n(v___x_571_, 11);
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_571_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__14));
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__16));
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__18));
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__20));
v___x_579_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__21));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_571_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22, &l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22_once, _init_l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__22);
v___x_582_ = l_Array_append___redArg(v___x_581_, v_args_570_);
lean_dec_ref(v_args_570_);
v___x_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_571_);
lean_ctor_set(v___x_583_, 1, v___x_577_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
v___x_584_ = l_Lean_Syntax_node2(v___x_571_, v___x_578_, v___x_580_, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__23));
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_571_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_588_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_571_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
v___x_590_ = l_Lean_Syntax_node2(v___x_571_, v___x_588_, v___x_589_, v___x_569_);
v___x_591_ = l_Lean_Syntax_node3(v___x_571_, v___x_577_, v___x_584_, v___x_586_, v___x_590_);
v___x_592_ = l_Lean_Syntax_node1(v___x_571_, v___x_576_, v___x_591_);
v___x_593_ = l_Lean_Syntax_node1(v___x_571_, v___x_575_, v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__26));
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_571_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_Syntax_node3(v___x_571_, v___x_572_, v___x_574_, v___x_593_, v___x_595_);
v___x_597_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_549_, v_mv_508_, v_val_545_, v___x_596_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_val_545_);
v___y_517_ = v___x_597_;
goto v___jp_516_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = l_Lean_Syntax_getArg(v_val_545_, v___x_598_);
v___x_600_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__28));
v___x_601_ = l_Lean_Syntax_isOfKind(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec(v_val_545_);
lean_dec(v_mv_508_);
v___x_602_ = lean_box(v___x_601_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
lean_ctor_set(v___x_547_, 0, v___x_602_);
v___x_604_ = v___x_547_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v_ref_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_del_object(v___x_547_);
v_ref_606_ = lean_ctor_get(v_a_513_, 2);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = l_Lean_Syntax_getArg(v_val_545_, v___x_607_);
v___x_609_ = 0;
v___x_610_ = l_Lean_SourceInfo_fromRef(v_ref_606_, v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__24));
v___x_612_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__25));
lean_inc(v___x_610_);
v___x_613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_610_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
v___x_614_ = l_Lean_Syntax_node2(v___x_610_, v___x_612_, v___x_613_, v___x_608_);
v___x_615_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___f_549_, v_mv_508_, v_val_545_, v___x_614_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_val_545_);
v___y_517_ = v___x_615_;
goto v___jp_516_;
}
}
}
}
else
{
uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v___x_544_);
lean_dec(v_mv_508_);
v___x_617_ = 0;
v___x_618_ = lean_box(v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
v___jp_516_:
{
if (lean_obj_tag(v___y_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_526_; 
v_a_518_ = lean_ctor_get(v___y_517_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___y_517_);
if (v_isSharedCheck_526_ == 0)
{
v___x_520_ = v___y_517_;
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___y_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_526_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_a_522_; lean_object* v___x_524_; 
v_a_522_ = lean_ctor_get(v_a_518_, 0);
lean_inc(v_a_522_);
lean_dec(v_a_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v_a_522_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_543_; 
v_a_527_ = lean_ctor_get(v___y_517_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___y_517_);
if (v_isSharedCheck_543_ == 0)
{
v___x_529_ = v___y_517_;
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___y_517_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_543_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_Exception_isInterrupt(v_a_527_);
if (v___x_531_ == 0)
{
uint8_t v___x_532_; 
lean_inc(v_a_527_);
v___x_532_ = l_Lean_Exception_isRuntime(v_a_527_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_535_; 
lean_dec(v_a_527_);
v___x_533_ = lean_box(v___x_532_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v___x_538_; 
if (v_isShared_530_ == 0)
{
v___x_538_ = v___x_529_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_527_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_object* v___x_541_; 
if (v_isShared_530_ == 0)
{
v___x_541_ = v___x_529_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_527_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_620_, lean_object* v_n_621_, lean_object* v_mv_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_620_, v_n_621_, v_mv_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_n_621_);
lean_dec_ref(v_invariantAlts_620_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_631_, lean_object* v_m_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_632_, v_a_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_635_, lean_object* v_m_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(v_00_u03b2_635_, v_m_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_m_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___redArg(v_mvarId_639_, v___y_643_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_mvarId_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v_mvarId_648_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_657_, lean_object* v_val_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_657_, v_val_658_, v___y_662_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_667_, lean_object* v_val_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_667_, v_val_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_677_, lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_681_, lean_object* v_a_682_, lean_object* v_x_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_681_, v_a_682_, v_x_683_);
lean_dec(v_x_683_);
lean_dec(v_a_682_);
return v_res_684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_689_, v_x_690_, v_x_691_);
lean_dec(v_x_691_);
lean_dec_ref(v_x_690_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, size_t v_x_701_, lean_object* v_x_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_700_, v_x_701_, v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
size_t v_x_15598__boxed_708_; uint8_t v_res_709_; lean_object* v_r_710_; 
v_x_15598__boxed_708_ = lean_unbox_usize(v_x_706_);
lean_dec(v_x_706_);
v_res_709_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_704_, v_x_705_, v_x_15598__boxed_708_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_x_705_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_711_, lean_object* v_x_712_, size_t v_x_713_, size_t v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_712_, v_x_713_, v_x_714_, v_x_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
size_t v_x_15609__boxed_724_; size_t v_x_15610__boxed_725_; lean_object* v_res_726_; 
v_x_15609__boxed_724_ = lean_unbox_usize(v_x_720_);
lean_dec(v_x_720_);
v_x_15610__boxed_725_ = lean_unbox_usize(v_x_721_);
lean_dec(v_x_721_);
v_res_726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_718_, v_x_719_, v_x_15609__boxed_724_, v_x_15610__boxed_725_, v_x_722_, v_x_723_);
return v_res_726_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_heq_730_, lean_object* v_i_731_, lean_object* v_k_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_728_, v_i_731_, v_k_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_734_, lean_object* v_keys_735_, lean_object* v_vals_736_, lean_object* v_heq_737_, lean_object* v_i_738_, lean_object* v_k_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_734_, v_keys_735_, v_vals_736_, v_heq_737_, v_i_738_, v_k_739_);
lean_dec(v_k_739_);
lean_dec_ref(v_vals_736_);
lean_dec_ref(v_keys_735_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_742_, lean_object* v_n_743_, lean_object* v_k_744_, lean_object* v_v_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_743_, v_k_744_, v_v_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_747_, size_t v_depth_748_, lean_object* v_keys_749_, lean_object* v_vals_750_, lean_object* v_heq_751_, lean_object* v_i_752_, lean_object* v_entries_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_748_, v_keys_749_, v_vals_750_, v_i_752_, v_entries_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_755_, lean_object* v_depth_756_, lean_object* v_keys_757_, lean_object* v_vals_758_, lean_object* v_heq_759_, lean_object* v_i_760_, lean_object* v_entries_761_){
_start:
{
size_t v_depth_boxed_762_; lean_object* v_res_763_; 
v_depth_boxed_762_ = lean_unbox_usize(v_depth_756_);
lean_dec(v_depth_756_);
v_res_763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_755_, v_depth_boxed_762_, v_keys_757_, v_vals_758_, v_heq_759_, v_i_760_, v_entries_761_);
lean_dec_ref(v_vals_758_);
lean_dec_ref(v_keys_757_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_765_, v_x_766_, v_x_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
return v_x_770_;
}
else
{
lean_object* v_key_772_; lean_object* v_value_773_; lean_object* v_tail_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_797_; 
v_key_772_ = lean_ctor_get(v_x_771_, 0);
v_value_773_ = lean_ctor_get(v_x_771_, 1);
v_tail_774_ = lean_ctor_get(v_x_771_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_797_ == 0)
{
v___x_776_ = v_x_771_;
v_isShared_777_ = v_isSharedCheck_797_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_tail_774_);
lean_inc(v_value_773_);
lean_inc(v_key_772_);
lean_dec(v_x_771_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_797_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; uint64_t v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v_fold_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_778_ = lean_array_get_size(v_x_770_);
v___x_779_ = lean_uint64_of_nat(v_key_772_);
v___x_780_ = 32ULL;
v___x_781_ = lean_uint64_shift_right(v___x_779_, v___x_780_);
v_fold_782_ = lean_uint64_xor(v___x_779_, v___x_781_);
v___x_783_ = 16ULL;
v___x_784_ = lean_uint64_shift_right(v_fold_782_, v___x_783_);
v___x_785_ = lean_uint64_xor(v_fold_782_, v___x_784_);
v___x_786_ = lean_uint64_to_usize(v___x_785_);
v___x_787_ = lean_usize_of_nat(v___x_778_);
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_sub(v___x_787_, v___x_788_);
v___x_790_ = lean_usize_land(v___x_786_, v___x_789_);
v___x_791_ = lean_array_uget_borrowed(v_x_770_, v___x_790_);
lean_inc(v___x_791_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v___x_791_);
v___x_793_ = v___x_776_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_key_772_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_value_773_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___x_791_);
v___x_793_ = v_reuseFailAlloc_796_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; 
v___x_794_ = lean_array_uset(v_x_770_, v___x_790_, v___x_793_);
v_x_770_ = v___x_794_;
v_x_771_ = v_tail_774_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_798_, lean_object* v_source_799_, lean_object* v_target_800_){
_start:
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = lean_array_get_size(v_source_799_);
v___x_802_ = lean_nat_dec_lt(v_i_798_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec_ref(v_source_799_);
lean_dec(v_i_798_);
return v_target_800_;
}
else
{
lean_object* v_es_803_; lean_object* v___x_804_; lean_object* v_source_805_; lean_object* v_target_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_es_803_ = lean_array_fget(v_source_799_, v_i_798_);
v___x_804_ = lean_box(0);
v_source_805_ = lean_array_fset(v_source_799_, v_i_798_, v___x_804_);
v_target_806_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_800_, v_es_803_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_i_798_, v___x_807_);
lean_dec(v_i_798_);
v_i_798_ = v___x_808_;
v_source_799_ = v_source_805_;
v_target_800_ = v_target_806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_nbuckets_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_811_ = lean_array_get_size(v_data_810_);
v___x_812_ = lean_unsigned_to_nat(2u);
v_nbuckets_813_ = lean_nat_mul(v___x_811_, v___x_812_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_box(0);
v___x_816_ = lean_mk_array(v_nbuckets_813_, v___x_815_);
v___x_817_ = lean_array_propagate_mark(v_data_810_, v___x_816_);
v___x_818_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_814_, v_data_810_, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
else
{
lean_object* v_key_822_; lean_object* v_tail_823_; uint8_t v___x_824_; 
v_key_822_ = lean_ctor_get(v_x_820_, 0);
v_tail_823_ = lean_ctor_get(v_x_820_, 2);
v___x_824_ = lean_nat_dec_eq(v_key_822_, v_a_819_);
if (v___x_824_ == 0)
{
v_x_820_ = v_tail_823_;
goto _start;
}
else
{
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_826_, lean_object* v_x_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_826_, v_x_827_);
lean_dec(v_x_827_);
lean_dec(v_a_826_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_830_, lean_object* v_a_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_size_833_; lean_object* v_buckets_834_; lean_object* v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; uint64_t v_fold_839_; uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v___x_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; lean_object* v_bkt_848_; uint8_t v___x_849_; 
v_size_833_ = lean_ctor_get(v_m_830_, 0);
v_buckets_834_ = lean_ctor_get(v_m_830_, 1);
v___x_835_ = lean_array_get_size(v_buckets_834_);
v___x_836_ = lean_uint64_of_nat(v_a_831_);
v___x_837_ = 32ULL;
v___x_838_ = lean_uint64_shift_right(v___x_836_, v___x_837_);
v_fold_839_ = lean_uint64_xor(v___x_836_, v___x_838_);
v___x_840_ = 16ULL;
v___x_841_ = lean_uint64_shift_right(v_fold_839_, v___x_840_);
v___x_842_ = lean_uint64_xor(v_fold_839_, v___x_841_);
v___x_843_ = lean_uint64_to_usize(v___x_842_);
v___x_844_ = lean_usize_of_nat(v___x_835_);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_sub(v___x_844_, v___x_845_);
v___x_847_ = lean_usize_land(v___x_843_, v___x_846_);
v_bkt_848_ = lean_array_uget_borrowed(v_buckets_834_, v___x_847_);
v___x_849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_831_, v_bkt_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_870_; 
lean_inc_ref(v_buckets_834_);
lean_inc(v_size_833_);
v_isSharedCheck_870_ = !lean_is_exclusive(v_m_830_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; lean_object* v_unused_872_; 
v_unused_871_ = lean_ctor_get(v_m_830_, 1);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_m_830_, 0);
lean_dec(v_unused_872_);
v___x_851_ = v_m_830_;
v_isShared_852_ = v_isSharedCheck_870_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_m_830_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_870_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v_size_x27_854_; lean_object* v___x_855_; lean_object* v_buckets_x27_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v_size_x27_854_ = lean_nat_add(v_size_833_, v___x_853_);
lean_dec(v_size_833_);
lean_inc(v_bkt_848_);
v___x_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_855_, 0, v_a_831_);
lean_ctor_set(v___x_855_, 1, v_b_832_);
lean_ctor_set(v___x_855_, 2, v_bkt_848_);
v_buckets_x27_856_ = lean_array_uset(v_buckets_834_, v___x_847_, v___x_855_);
v___x_857_ = lean_unsigned_to_nat(4u);
v___x_858_ = lean_nat_mul(v_size_x27_854_, v___x_857_);
v___x_859_ = lean_unsigned_to_nat(3u);
v___x_860_ = lean_nat_div(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_array_get_size(v_buckets_x27_856_);
v___x_862_ = lean_nat_dec_le(v___x_860_, v___x_861_);
lean_dec(v___x_860_);
if (v___x_862_ == 0)
{
lean_object* v_val_863_; lean_object* v___x_865_; 
v_val_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_856_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_val_863_);
lean_ctor_set(v___x_851_, 0, v_size_x27_854_);
v___x_865_ = v___x_851_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_size_x27_854_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_val_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v___x_868_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_buckets_x27_856_);
lean_ctor_set(v___x_851_, 0, v_size_x27_854_);
v___x_868_ = v___x_851_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_size_x27_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_buckets_x27_856_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_dec(v_b_832_);
lean_dec(v_a_831_);
return v_m_830_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_873_, lean_object* v_as_x27_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
if (lean_obj_tag(v_as_x27_874_) == 0)
{
lean_object* v___x_885_; 
lean_dec_ref(v___x_873_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_b_875_);
return v___x_885_;
}
else
{
lean_object* v_head_886_; lean_object* v_tail_887_; lean_object* v___x_888_; 
v_head_886_ = lean_ctor_get(v_as_x27_874_, 0);
v_tail_887_ = lean_ctor_get(v_as_x27_874_, 1);
lean_inc(v_head_886_);
v___x_888_ = l_Lean_MVarId_getType(v_head_886_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; uint8_t v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
lean_inc_ref(v___x_873_);
v___x_890_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_873_, v_a_889_);
lean_dec(v_a_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_inc(v_head_886_);
v___x_891_ = lean_array_push(v_b_875_, v_head_886_);
v_as_x27_874_ = v_tail_887_;
v_b_875_ = v___x_891_;
goto _start;
}
else
{
lean_object* v___x_893_; lean_object* v_invariants_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_specBackwardRuleCache_899_; lean_object* v_splitBackwardRuleCache_900_; lean_object* v_latticeBackwardRuleCache_901_; lean_object* v_frameBackwardRuleCache_902_; lean_object* v_frameDB_903_; lean_object* v_invariants_904_; lean_object* v_vcs_905_; lean_object* v_simpState_906_; lean_object* v_fuel_907_; lean_object* v_inlineHandledInvariants_908_; lean_object* v_pendingJoinPoints_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_964_; 
v___x_893_ = lean_st_ref_get(v___y_877_);
v_invariants_894_ = lean_ctor_get(v___x_893_, 5);
lean_inc_ref(v_invariants_894_);
lean_dec(v___x_893_);
v___x_895_ = lean_array_get_size(v_invariants_894_);
lean_dec_ref(v_invariants_894_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_add(v___x_895_, v___x_896_);
v___x_898_ = lean_st_ref_take(v___y_877_);
v_specBackwardRuleCache_899_ = lean_ctor_get(v___x_898_, 0);
v_splitBackwardRuleCache_900_ = lean_ctor_get(v___x_898_, 1);
v_latticeBackwardRuleCache_901_ = lean_ctor_get(v___x_898_, 2);
v_frameBackwardRuleCache_902_ = lean_ctor_get(v___x_898_, 3);
v_frameDB_903_ = lean_ctor_get(v___x_898_, 4);
v_invariants_904_ = lean_ctor_get(v___x_898_, 5);
v_vcs_905_ = lean_ctor_get(v___x_898_, 6);
v_simpState_906_ = lean_ctor_get(v___x_898_, 7);
v_fuel_907_ = lean_ctor_get(v___x_898_, 8);
v_inlineHandledInvariants_908_ = lean_ctor_get(v___x_898_, 9);
v_pendingJoinPoints_909_ = lean_ctor_get(v___x_898_, 10);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_964_ == 0)
{
v___x_911_ = v___x_898_;
v_isShared_912_ = v_isSharedCheck_964_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_pendingJoinPoints_909_);
lean_inc(v_inlineHandledInvariants_908_);
lean_inc(v_fuel_907_);
lean_inc(v_simpState_906_);
lean_inc(v_vcs_905_);
lean_inc(v_invariants_904_);
lean_inc(v_frameDB_903_);
lean_inc(v_frameBackwardRuleCache_902_);
lean_inc(v_latticeBackwardRuleCache_901_);
lean_inc(v_splitBackwardRuleCache_900_);
lean_inc(v_specBackwardRuleCache_899_);
lean_dec(v___x_898_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_964_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_inc(v_head_886_);
v___x_913_ = lean_array_push(v_invariants_904_, v_head_886_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 5, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_specBackwardRuleCache_899_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_splitBackwardRuleCache_900_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_latticeBackwardRuleCache_901_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_frameBackwardRuleCache_902_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_frameDB_903_);
lean_ctor_set(v_reuseFailAlloc_963_, 5, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_963_, 6, v_vcs_905_);
lean_ctor_set(v_reuseFailAlloc_963_, 7, v_simpState_906_);
lean_ctor_set(v_reuseFailAlloc_963_, 8, v_fuel_907_);
lean_ctor_set(v_reuseFailAlloc_963_, 9, v_inlineHandledInvariants_908_);
lean_ctor_set(v_reuseFailAlloc_963_, 10, v_pendingJoinPoints_909_);
v___x_915_ = v_reuseFailAlloc_963_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v_invariantAlts_917_; lean_object* v___x_918_; 
v___x_916_ = lean_st_ref_put(v___y_877_, v___x_915_);
v_invariantAlts_917_ = lean_ctor_get(v___y_876_, 3);
lean_inc(v_head_886_);
v___x_918_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_invariantAlts_917_, v___x_897_, v_head_886_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; uint8_t v___x_920_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; lean_object* v___x_922_; 
lean_dec(v___x_897_);
v___x_921_ = 2;
lean_inc(v_head_886_);
v___x_922_ = l_Lean_MVarId_setKind___redArg(v_head_886_, v___x_921_, v___y_881_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref_known(v___x_922_, 1);
v_as_x27_874_ = v_tail_887_;
goto _start;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_b_875_);
lean_dec_ref(v___x_873_);
v_a_924_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v_specBackwardRuleCache_933_; lean_object* v_splitBackwardRuleCache_934_; lean_object* v_latticeBackwardRuleCache_935_; lean_object* v_frameBackwardRuleCache_936_; lean_object* v_frameDB_937_; lean_object* v_invariants_938_; lean_object* v_vcs_939_; lean_object* v_simpState_940_; lean_object* v_fuel_941_; lean_object* v_inlineHandledInvariants_942_; lean_object* v_pendingJoinPoints_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_954_; 
v___x_932_ = lean_st_ref_take(v___y_877_);
v_specBackwardRuleCache_933_ = lean_ctor_get(v___x_932_, 0);
v_splitBackwardRuleCache_934_ = lean_ctor_get(v___x_932_, 1);
v_latticeBackwardRuleCache_935_ = lean_ctor_get(v___x_932_, 2);
v_frameBackwardRuleCache_936_ = lean_ctor_get(v___x_932_, 3);
v_frameDB_937_ = lean_ctor_get(v___x_932_, 4);
v_invariants_938_ = lean_ctor_get(v___x_932_, 5);
v_vcs_939_ = lean_ctor_get(v___x_932_, 6);
v_simpState_940_ = lean_ctor_get(v___x_932_, 7);
v_fuel_941_ = lean_ctor_get(v___x_932_, 8);
v_inlineHandledInvariants_942_ = lean_ctor_get(v___x_932_, 9);
v_pendingJoinPoints_943_ = lean_ctor_get(v___x_932_, 10);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_954_ == 0)
{
v___x_945_ = v___x_932_;
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_pendingJoinPoints_943_);
lean_inc(v_inlineHandledInvariants_942_);
lean_inc(v_fuel_941_);
lean_inc(v_simpState_940_);
lean_inc(v_vcs_939_);
lean_inc(v_invariants_938_);
lean_inc(v_frameDB_937_);
lean_inc(v_frameBackwardRuleCache_936_);
lean_inc(v_latticeBackwardRuleCache_935_);
lean_inc(v_splitBackwardRuleCache_934_);
lean_inc(v_specBackwardRuleCache_933_);
lean_dec(v___x_932_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_947_ = lean_box(0);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_942_, v___x_897_, v___x_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 9, v___x_948_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_specBackwardRuleCache_933_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_splitBackwardRuleCache_934_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_latticeBackwardRuleCache_935_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_frameBackwardRuleCache_936_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_frameDB_937_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_invariants_938_);
lean_ctor_set(v_reuseFailAlloc_953_, 6, v_vcs_939_);
lean_ctor_set(v_reuseFailAlloc_953_, 7, v_simpState_940_);
lean_ctor_set(v_reuseFailAlloc_953_, 8, v_fuel_941_);
lean_ctor_set(v_reuseFailAlloc_953_, 9, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 10, v_pendingJoinPoints_943_);
v___x_950_ = v_reuseFailAlloc_953_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_st_ref_put(v___y_877_, v___x_950_);
v_as_x27_874_ = v_tail_887_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v___x_897_);
lean_dec_ref(v_b_875_);
lean_dec_ref(v___x_873_);
v_a_955_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_918_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_918_);
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
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_b_875_);
lean_dec_ref(v___x_873_);
v_a_965_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_888_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_888_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_973_, lean_object* v_as_x27_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_973_, v_as_x27_974_, v_b_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v_as_x27_974_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v_env_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = lean_st_ref_get(v_a_999_);
v_env_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc_ref(v_env_1002_);
lean_dec(v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1004_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_1002_, v_subgoals_988_, v___x_1003_, v_a_989_, v_a_990_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_subgoals_1005_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1019_, lean_object* v_m_1020_, lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1020_, v_a_1021_, v_b_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1024_, lean_object* v_as_1025_, lean_object* v_as_x27_1026_, lean_object* v_b_1027_, lean_object* v_a_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1024_, v_as_x27_1026_, v_b_1027_, v___y_1029_, v___y_1030_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1042_ = _args[0];
lean_object* v_as_1043_ = _args[1];
lean_object* v_as_x27_1044_ = _args[2];
lean_object* v_b_1045_ = _args[3];
lean_object* v_a_1046_ = _args[4];
lean_object* v___y_1047_ = _args[5];
lean_object* v___y_1048_ = _args[6];
lean_object* v___y_1049_ = _args[7];
lean_object* v___y_1050_ = _args[8];
lean_object* v___y_1051_ = _args[9];
lean_object* v___y_1052_ = _args[10];
lean_object* v___y_1053_ = _args[11];
lean_object* v___y_1054_ = _args[12];
lean_object* v___y_1055_ = _args[13];
lean_object* v___y_1056_ = _args[14];
lean_object* v___y_1057_ = _args[15];
lean_object* v___y_1058_ = _args[16];
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__1(v___x_1042_, v_as_1043_, v_as_x27_1044_, v_b_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_as_x27_1044_);
lean_dec(v_as_1043_);
return v_res_1059_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1061_, v_x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1064_, lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1064_, v_a_1065_, v_x_1066_);
lean_dec(v_x_1066_);
lean_dec(v_a_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1069_, lean_object* v_data_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1072_, lean_object* v_i_1073_, lean_object* v_source_1074_, lean_object* v_target_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1073_, v_source_1074_, v_target_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_toGoalState_1094_; lean_object* v_mvarId_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1192_; 
v_toGoalState_1094_ = lean_ctor_get(v_goal_1081_, 0);
v_mvarId_1095_ = lean_ctor_get(v_goal_1081_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_goal_1081_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1097_ = v_goal_1081_;
v_isShared_1098_ = v_isSharedCheck_1192_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_mvarId_1095_);
lean_inc(v_toGoalState_1094_);
lean_dec(v_goal_1081_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1192_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1095_, v_a_1082_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 1, v_a_1100_);
v___x_1102_ = v___x_1097_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_toGoalState_1094_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_a_1100_);
v___x_1102_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v___x_1102_, v_a_1082_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1174_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1174_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1174_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_toGoalState_1108_; uint8_t v_inconsistent_1109_; 
v_toGoalState_1108_ = lean_ctor_get(v_a_1104_, 0);
lean_inc_ref(v_toGoalState_1108_);
v_inconsistent_1109_ = lean_ctor_get_uint8(v_toGoalState_1108_, sizeof(void*)*19);
if (v_inconsistent_1109_ == 0)
{
lean_object* v_mvarId_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1168_; 
lean_del_object(v___x_1106_);
v_mvarId_1110_ = lean_ctor_get(v_a_1104_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_a_1104_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_a_1104_, 0);
lean_dec(v_unused_1169_);
v___x_1112_ = v_a_1104_;
v_isShared_1113_ = v_isSharedCheck_1168_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_mvarId_1110_);
lean_dec(v_a_1104_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1168_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_mvarId_1110_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1159_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1159_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1159_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
if (lean_obj_tag(v_a_1115_) == 1)
{
lean_object* v_val_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1117_);
v_val_1119_ = lean_ctor_get(v_a_1115_, 0);
lean_inc_n(v_val_1119_, 2);
lean_dec_ref_known(v_a_1115_, 1);
v___x_1120_ = 2;
v___x_1121_ = l_Lean_MVarId_setKind___redArg(v_val_1119_, v___x_1120_, v_a_1090_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1153_; 
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1154_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1153_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1153_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v_specBackwardRuleCache_1126_; lean_object* v_splitBackwardRuleCache_1127_; lean_object* v_latticeBackwardRuleCache_1128_; lean_object* v_frameBackwardRuleCache_1129_; lean_object* v_frameDB_1130_; lean_object* v_invariants_1131_; lean_object* v_vcs_1132_; lean_object* v_simpState_1133_; lean_object* v_fuel_1134_; lean_object* v_inlineHandledInvariants_1135_; lean_object* v_pendingJoinPoints_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1152_; 
v___x_1125_ = lean_st_ref_take(v_a_1083_);
v_specBackwardRuleCache_1126_ = lean_ctor_get(v___x_1125_, 0);
v_splitBackwardRuleCache_1127_ = lean_ctor_get(v___x_1125_, 1);
v_latticeBackwardRuleCache_1128_ = lean_ctor_get(v___x_1125_, 2);
v_frameBackwardRuleCache_1129_ = lean_ctor_get(v___x_1125_, 3);
v_frameDB_1130_ = lean_ctor_get(v___x_1125_, 4);
v_invariants_1131_ = lean_ctor_get(v___x_1125_, 5);
v_vcs_1132_ = lean_ctor_get(v___x_1125_, 6);
v_simpState_1133_ = lean_ctor_get(v___x_1125_, 7);
v_fuel_1134_ = lean_ctor_get(v___x_1125_, 8);
v_inlineHandledInvariants_1135_ = lean_ctor_get(v___x_1125_, 9);
v_pendingJoinPoints_1136_ = lean_ctor_get(v___x_1125_, 10);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1138_ = v___x_1125_;
v_isShared_1139_ = v_isSharedCheck_1152_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_pendingJoinPoints_1136_);
lean_inc(v_inlineHandledInvariants_1135_);
lean_inc(v_fuel_1134_);
lean_inc(v_simpState_1133_);
lean_inc(v_vcs_1132_);
lean_inc(v_invariants_1131_);
lean_inc(v_frameDB_1130_);
lean_inc(v_frameBackwardRuleCache_1129_);
lean_inc(v_latticeBackwardRuleCache_1128_);
lean_inc(v_splitBackwardRuleCache_1127_);
lean_inc(v_specBackwardRuleCache_1126_);
lean_dec(v___x_1125_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1152_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(0);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_val_1119_);
v___x_1142_ = v___x_1112_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_toGoalState_1108_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_val_1119_);
v___x_1142_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_array_push(v_vcs_1132_, v___x_1142_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 6, v___x_1143_);
v___x_1145_ = v___x_1138_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_specBackwardRuleCache_1126_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v_splitBackwardRuleCache_1127_);
lean_ctor_set(v_reuseFailAlloc_1150_, 2, v_latticeBackwardRuleCache_1128_);
lean_ctor_set(v_reuseFailAlloc_1150_, 3, v_frameBackwardRuleCache_1129_);
lean_ctor_set(v_reuseFailAlloc_1150_, 4, v_frameDB_1130_);
lean_ctor_set(v_reuseFailAlloc_1150_, 5, v_invariants_1131_);
lean_ctor_set(v_reuseFailAlloc_1150_, 6, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 7, v_simpState_1133_);
lean_ctor_set(v_reuseFailAlloc_1150_, 8, v_fuel_1134_);
lean_ctor_set(v_reuseFailAlloc_1150_, 9, v_inlineHandledInvariants_1135_);
lean_ctor_set(v_reuseFailAlloc_1150_, 10, v_pendingJoinPoints_1136_);
v___x_1145_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_st_ref_put(v_a_1083_, v___x_1145_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1140_);
v___x_1148_ = v___x_1123_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1140_);
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
}
}
else
{
lean_dec(v_val_1119_);
lean_del_object(v___x_1112_);
lean_dec_ref(v_toGoalState_1108_);
return v___x_1121_;
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec(v_a_1115_);
lean_del_object(v___x_1112_);
lean_dec_ref(v_toGoalState_1108_);
v___x_1155_ = lean_box(0);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1155_);
v___x_1157_ = v___x_1117_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_del_object(v___x_1112_);
lean_dec_ref(v_toGoalState_1108_);
v_a_1160_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1114_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1114_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
lean_dec_ref(v_toGoalState_1108_);
lean_dec(v_a_1104_);
v___x_1170_ = lean_box(0);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1170_);
v___x_1172_ = v___x_1106_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1103_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1103_);
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
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_del_object(v___x_1097_);
lean_dec_ref(v_toGoalState_1094_);
v_a_1184_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1099_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1099_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(lean_object* v_a_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
else
{
lean_object* v_key_1210_; lean_object* v_tail_1211_; uint8_t v___x_1212_; 
v_key_1210_ = lean_ctor_get(v_x_1208_, 0);
v_tail_1211_ = lean_ctor_get(v_x_1208_, 2);
v___x_1212_ = l_Lean_instBEqMVarId_beq(v_key_1210_, v_a_1207_);
if (v___x_1212_ == 0)
{
v_x_1208_ = v_tail_1211_;
goto _start;
}
else
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg___boxed(lean_object* v_a_1214_, lean_object* v_x_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(v_a_1214_, v_x_1215_);
lean_dec(v_x_1215_);
lean_dec(v_a_1214_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(lean_object* v_a_1218_, lean_object* v_x_1219_){
_start:
{
if (lean_obj_tag(v_x_1219_) == 0)
{
return v_x_1219_;
}
else
{
lean_object* v_key_1220_; lean_object* v_value_1221_; lean_object* v_tail_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1231_; 
v_key_1220_ = lean_ctor_get(v_x_1219_, 0);
v_value_1221_ = lean_ctor_get(v_x_1219_, 1);
v_tail_1222_ = lean_ctor_get(v_x_1219_, 2);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_x_1219_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1224_ = v_x_1219_;
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_tail_1222_);
lean_inc(v_value_1221_);
lean_inc(v_key_1220_);
lean_dec(v_x_1219_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Lean_instBEqMVarId_beq(v_key_1220_, v_a_1218_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1218_, v_tail_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 2, v___x_1227_);
v___x_1229_ = v___x_1224_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_key_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_value_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
else
{
lean_del_object(v___x_1224_);
lean_dec(v_value_1221_);
lean_dec(v_key_1220_);
return v_tail_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg___boxed(lean_object* v_a_1232_, lean_object* v_x_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1232_, v_x_1233_);
lean_dec(v_a_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(lean_object* v_m_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_size_1237_; lean_object* v_buckets_1238_; lean_object* v___x_1239_; uint64_t v___x_1240_; uint64_t v___x_1241_; uint64_t v___x_1242_; uint64_t v_fold_1243_; uint64_t v___x_1244_; uint64_t v___x_1245_; uint64_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v_bkt_1252_; uint8_t v___x_1253_; 
v_size_1237_ = lean_ctor_get(v_m_1235_, 0);
v_buckets_1238_ = lean_ctor_get(v_m_1235_, 1);
v___x_1239_ = lean_array_get_size(v_buckets_1238_);
v___x_1240_ = l_Lean_instHashableMVarId_hash(v_a_1236_);
v___x_1241_ = 32ULL;
v___x_1242_ = lean_uint64_shift_right(v___x_1240_, v___x_1241_);
v_fold_1243_ = lean_uint64_xor(v___x_1240_, v___x_1242_);
v___x_1244_ = 16ULL;
v___x_1245_ = lean_uint64_shift_right(v_fold_1243_, v___x_1244_);
v___x_1246_ = lean_uint64_xor(v_fold_1243_, v___x_1245_);
v___x_1247_ = lean_uint64_to_usize(v___x_1246_);
v___x_1248_ = lean_usize_of_nat(v___x_1239_);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_sub(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_usize_land(v___x_1247_, v___x_1250_);
v_bkt_1252_ = lean_array_uget_borrowed(v_buckets_1238_, v___x_1251_);
v___x_1253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(v_a_1236_, v_bkt_1252_);
if (v___x_1253_ == 0)
{
return v_m_1235_;
}
else
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1266_; 
lean_inc(v_bkt_1252_);
lean_inc_ref(v_buckets_1238_);
lean_inc(v_size_1237_);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_m_1235_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; lean_object* v_unused_1268_; 
v_unused_1267_ = lean_ctor_get(v_m_1235_, 1);
lean_dec(v_unused_1267_);
v_unused_1268_ = lean_ctor_get(v_m_1235_, 0);
lean_dec(v_unused_1268_);
v___x_1255_ = v_m_1235_;
v_isShared_1256_ = v_isSharedCheck_1266_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v_m_1235_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1266_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v_buckets_x27_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1257_ = lean_box(0);
v_buckets_x27_1258_ = lean_array_uset(v_buckets_1238_, v___x_1251_, v___x_1257_);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_sub(v_size_1237_, v___x_1259_);
lean_dec(v_size_1237_);
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1236_, v_bkt_1252_);
v___x_1262_ = lean_array_uset(v_buckets_x27_1258_, v___x_1251_, v___x_1261_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v___x_1262_);
lean_ctor_set(v___x_1255_, 0, v___x_1260_);
v___x_1264_ = v___x_1255_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg___boxed(lean_object* v_m_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(v_m_1269_, v_a_1270_);
lean_dec(v_a_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(lean_object* v_mvarId_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v_mctx_1276_; lean_object* v_eAssignment_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1275_ = lean_st_ref_get(v___y_1273_);
v_mctx_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc_ref(v_mctx_1276_);
lean_dec(v___x_1275_);
v_eAssignment_1277_ = lean_ctor_get(v_mctx_1276_, 8);
lean_inc_ref(v_eAssignment_1277_);
lean_dec_ref(v_mctx_1276_);
v___x_1278_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1277_, v_mvarId_1272_);
lean_dec_ref(v_eAssignment_1277_);
v___x_1279_ = lean_box(v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg___boxed(lean_object* v_mvarId_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(v_mvarId_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec(v_mvarId_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(lean_object* v_a_1285_, lean_object* v_x_1286_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_box(0);
return v___x_1287_;
}
else
{
lean_object* v_key_1288_; lean_object* v_value_1289_; lean_object* v_tail_1290_; uint8_t v___x_1291_; 
v_key_1288_ = lean_ctor_get(v_x_1286_, 0);
v_value_1289_ = lean_ctor_get(v_x_1286_, 1);
v_tail_1290_ = lean_ctor_get(v_x_1286_, 2);
v___x_1291_ = l_Lean_instBEqMVarId_beq(v_key_1288_, v_a_1285_);
if (v___x_1291_ == 0)
{
v_x_1286_ = v_tail_1290_;
goto _start;
}
else
{
lean_object* v___x_1293_; 
lean_inc(v_value_1289_);
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_value_1289_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg___boxed(lean_object* v_a_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(v_a_1294_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec(v_a_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_m_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_buckets_1299_; lean_object* v___x_1300_; uint64_t v___x_1301_; uint64_t v___x_1302_; uint64_t v___x_1303_; uint64_t v_fold_1304_; uint64_t v___x_1305_; uint64_t v___x_1306_; uint64_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_buckets_1299_ = lean_ctor_get(v_m_1297_, 1);
v___x_1300_ = lean_array_get_size(v_buckets_1299_);
v___x_1301_ = l_Lean_instHashableMVarId_hash(v_a_1298_);
v___x_1302_ = 32ULL;
v___x_1303_ = lean_uint64_shift_right(v___x_1301_, v___x_1302_);
v_fold_1304_ = lean_uint64_xor(v___x_1301_, v___x_1303_);
v___x_1305_ = 16ULL;
v___x_1306_ = lean_uint64_shift_right(v_fold_1304_, v___x_1305_);
v___x_1307_ = lean_uint64_xor(v_fold_1304_, v___x_1306_);
v___x_1308_ = lean_uint64_to_usize(v___x_1307_);
v___x_1309_ = lean_usize_of_nat(v___x_1300_);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_sub(v___x_1309_, v___x_1310_);
v___x_1312_ = lean_usize_land(v___x_1308_, v___x_1311_);
v___x_1313_ = lean_array_uget_borrowed(v_buckets_1299_, v___x_1312_);
v___x_1314_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(v_a_1298_, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_m_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_m_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_m_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v___x_1318_, lean_object* v_scope_1319_, size_t v_sz_1320_, size_t v_i_1321_, lean_object* v_bs_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_lt(v_i_1321_, v_sz_1320_);
if (v___x_1323_ == 0)
{
lean_dec_ref(v_scope_1319_);
lean_dec_ref(v___x_1318_);
return v_bs_1322_;
}
else
{
lean_object* v_v_1324_; lean_object* v___x_1325_; lean_object* v_bs_x27_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v_v_1324_ = lean_array_uget(v_bs_1322_, v_i_1321_);
v___x_1325_ = lean_unsigned_to_nat(0u);
v_bs_x27_1326_ = lean_array_uset(v_bs_1322_, v_i_1321_, v___x_1325_);
lean_inc_ref(v___x_1318_);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1318_);
lean_ctor_set(v___x_1327_, 1, v_v_1324_);
lean_inc_ref(v_scope_1319_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_scope_1319_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1321_, v___x_1329_);
v___x_1331_ = lean_array_uset(v_bs_x27_1326_, v_i_1321_, v___x_1328_);
v_i_1321_ = v___x_1330_;
v_bs_1322_ = v___x_1331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v___x_1333_, lean_object* v_scope_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_bs_1337_){
_start:
{
size_t v_sz_boxed_1338_; size_t v_i_boxed_1339_; lean_object* v_res_1340_; 
v_sz_boxed_1338_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1339_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v___x_1333_, v_scope_1334_, v_sz_boxed_1338_, v_i_boxed_1339_, v_bs_1337_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(lean_object* v_goal_1341_, lean_object* v_scope_1342_, lean_object* v___x_1343_, lean_object* v_____r_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1341_, v___y_1345_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1429_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1429_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1429_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v_toGoalState_1362_; uint8_t v_inconsistent_1363_; 
v_toGoalState_1362_ = lean_ctor_get(v_a_1358_, 0);
v_inconsistent_1363_ = lean_ctor_get_uint8(v_toGoalState_1362_, sizeof(void*)*19);
if (v_inconsistent_1363_ == 0)
{
lean_object* v_mvarId_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1360_);
v_mvarId_1364_ = lean_ctor_get(v_a_1358_, 1);
lean_inc(v_mvarId_1364_);
v___x_1365_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1342_, v_mvarId_1364_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
if (lean_obj_tag(v_a_1366_) == 0)
{
lean_object* v_scope_1367_; lean_object* v_subgoals_1368_; lean_object* v___x_1369_; 
lean_inc_ref(v_toGoalState_1362_);
lean_dec(v_a_1358_);
v_scope_1367_ = lean_ctor_get(v_a_1366_, 0);
lean_inc_ref(v_scope_1367_);
v_subgoals_1368_ = lean_ctor_get(v_a_1366_, 1);
lean_inc(v_subgoals_1368_);
lean_dec_ref_known(v_a_1366_, 2);
v___x_1369_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1368_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v_subgoals_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1383_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1383_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1383_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; size_t v_sz_1375_; size_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1374_ = l_Array_reverse___redArg(v_a_1370_);
v_sz_1375_ = lean_array_size(v___x_1374_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_toGoalState_1362_, v_scope_1367_, v_sz_1375_, v___x_1376_, v___x_1374_);
v___x_1378_ = l_Array_append___redArg(v___x_1343_, v___x_1377_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1379_);
v___x_1381_ = v___x_1372_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_scope_1367_);
lean_dec_ref(v_toGoalState_1362_);
lean_dec_ref(v___x_1343_);
v_a_1384_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1369_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1369_);
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
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1415_; 
v_isSharedCheck_1415_ = !lean_is_exclusive(v_a_1366_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_a_1366_, 0);
lean_dec(v_unused_1416_);
v___x_1393_ = v_a_1366_;
v_isShared_1394_ = v_isSharedCheck_1415_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v_a_1366_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1415_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1358_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1405_; 
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1395_, 0);
lean_dec(v_unused_1406_);
v___x_1397_ = v___x_1395_;
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v___x_1395_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1343_);
v___x_1400_ = v___x_1393_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1343_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1400_);
v___x_1402_ = v___x_1397_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
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
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_del_object(v___x_1393_);
lean_dec_ref(v___x_1343_);
v_a_1407_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1395_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1395_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_a_1358_);
lean_dec_ref(v___x_1343_);
v_a_1417_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1365_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1365_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_dec(v_a_1358_);
lean_dec_ref(v_scope_1342_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1343_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1425_);
v___x_1427_ = v___x_1360_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v___x_1343_);
lean_dec_ref(v_scope_1342_);
v_a_1430_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1357_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1357_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0___boxed(lean_object* v_goal_1438_, lean_object* v_scope_1439_, lean_object* v___x_1440_, lean_object* v_____r_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(v_goal_1438_, v_scope_1439_, v___x_1440_, v_____r_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___y_1469_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_array_get_size(v_a_1455_);
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_sub(v___x_1489_, v___x_1490_);
v___x_1492_ = lean_nat_dec_lt(v___x_1491_, v___x_1489_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; 
lean_dec(v___x_1491_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v_a_1455_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v_goal_1495_; lean_object* v_scope_1496_; lean_object* v_mvarId_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1494_ = lean_array_fget_borrowed(v_a_1455_, v___x_1491_);
lean_dec(v___x_1491_);
v_goal_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_goal_1495_);
v_scope_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc_ref(v_scope_1496_);
v_mvarId_1497_ = lean_ctor_get(v_goal_1495_, 1);
v___x_1498_ = lean_array_pop(v_a_1455_);
v___x_1499_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(v_mvarId_1497_, v___y_1464_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; uint8_t v___x_1501_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = lean_unbox(v_a_1500_);
lean_dec(v_a_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v_pendingJoinPoints_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_st_ref_get(v___y_1457_);
v_pendingJoinPoints_1503_ = lean_ctor_get(v___x_1502_, 10);
lean_inc_ref(v_pendingJoinPoints_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_pendingJoinPoints_1503_, v_mvarId_1497_);
lean_dec_ref(v_pendingJoinPoints_1503_);
if (lean_obj_tag(v___x_1504_) == 1)
{
lean_object* v_val_1505_; lean_object* v_fst_1506_; lean_object* v_snd_1507_; lean_object* v___x_1508_; lean_object* v_specBackwardRuleCache_1509_; lean_object* v_splitBackwardRuleCache_1510_; lean_object* v_latticeBackwardRuleCache_1511_; lean_object* v_frameBackwardRuleCache_1512_; lean_object* v_frameDB_1513_; lean_object* v_invariants_1514_; lean_object* v_vcs_1515_; lean_object* v_simpState_1516_; lean_object* v_fuel_1517_; lean_object* v_inlineHandledInvariants_1518_; lean_object* v_pendingJoinPoints_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1539_; 
v_val_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v_fst_1506_ = lean_ctor_get(v_val_1505_, 0);
lean_inc(v_fst_1506_);
v_snd_1507_ = lean_ctor_get(v_val_1505_, 1);
lean_inc(v_snd_1507_);
lean_dec(v_val_1505_);
v___x_1508_ = lean_st_ref_take(v___y_1457_);
v_specBackwardRuleCache_1509_ = lean_ctor_get(v___x_1508_, 0);
v_splitBackwardRuleCache_1510_ = lean_ctor_get(v___x_1508_, 1);
v_latticeBackwardRuleCache_1511_ = lean_ctor_get(v___x_1508_, 2);
v_frameBackwardRuleCache_1512_ = lean_ctor_get(v___x_1508_, 3);
v_frameDB_1513_ = lean_ctor_get(v___x_1508_, 4);
v_invariants_1514_ = lean_ctor_get(v___x_1508_, 5);
v_vcs_1515_ = lean_ctor_get(v___x_1508_, 6);
v_simpState_1516_ = lean_ctor_get(v___x_1508_, 7);
v_fuel_1517_ = lean_ctor_get(v___x_1508_, 8);
v_inlineHandledInvariants_1518_ = lean_ctor_get(v___x_1508_, 9);
v_pendingJoinPoints_1519_ = lean_ctor_get(v___x_1508_, 10);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1521_ = v___x_1508_;
v_isShared_1522_ = v_isSharedCheck_1539_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_pendingJoinPoints_1519_);
lean_inc(v_inlineHandledInvariants_1518_);
lean_inc(v_fuel_1517_);
lean_inc(v_simpState_1516_);
lean_inc(v_vcs_1515_);
lean_inc(v_invariants_1514_);
lean_inc(v_frameDB_1513_);
lean_inc(v_frameBackwardRuleCache_1512_);
lean_inc(v_latticeBackwardRuleCache_1511_);
lean_inc(v_splitBackwardRuleCache_1510_);
lean_inc(v_specBackwardRuleCache_1509_);
lean_dec(v___x_1508_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1539_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(v_pendingJoinPoints_1519_, v_mvarId_1497_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 10, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_specBackwardRuleCache_1509_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_splitBackwardRuleCache_1510_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_latticeBackwardRuleCache_1511_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_frameBackwardRuleCache_1512_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_frameDB_1513_);
lean_ctor_set(v_reuseFailAlloc_1538_, 5, v_invariants_1514_);
lean_ctor_set(v_reuseFailAlloc_1538_, 6, v_vcs_1515_);
lean_ctor_set(v_reuseFailAlloc_1538_, 7, v_simpState_1516_);
lean_ctor_set(v_reuseFailAlloc_1538_, 8, v_fuel_1517_);
lean_ctor_set(v_reuseFailAlloc_1538_, 9, v_inlineHandledInvariants_1518_);
lean_ctor_set(v_reuseFailAlloc_1538_, 10, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_st_ref_put(v___y_1457_, v___x_1525_);
v___x_1527_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_fst_1506_, v_snd_1507_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1529_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(v_goal_1495_, v_scope_1496_, v___x_1498_, v_a_1528_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
v___y_1469_ = v___x_1529_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v___x_1498_);
lean_dec_ref(v_scope_1496_);
lean_dec_ref(v_goal_1495_);
v_a_1530_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1527_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1527_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v___x_1504_);
v___x_1540_ = lean_box(0);
v___x_1541_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(v_goal_1495_, v_scope_1496_, v___x_1498_, v___x_1540_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
v___y_1469_ = v___x_1541_;
goto v___jp_1468_;
}
}
else
{
lean_dec_ref(v_scope_1496_);
lean_dec_ref(v_goal_1495_);
v_a_1455_ = v___x_1498_;
goto _start;
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref(v___x_1498_);
lean_dec_ref(v_scope_1496_);
lean_dec_ref(v_goal_1495_);
v_a_1543_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1499_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1499_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
v___jp_1468_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v___y_1469_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___y_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
if (lean_obj_tag(v_a_1470_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; 
v_a_1474_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v_a_1470_, 1);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v_a_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
else
{
lean_object* v_a_1478_; 
lean_del_object(v___x_1472_);
v_a_1478_ = lean_ctor_get(v_a_1470_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v_a_1470_, 1);
v_a_1455_ = v_a_1478_;
goto _start;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___y_1469_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___y_1469_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___boxed(lean_object* v_a_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(v_a_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1565_, lean_object* v_goal_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_toGoalState_1579_; lean_object* v_mvarId_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1619_; 
v_toGoalState_1579_ = lean_ctor_get(v_goal_1566_, 0);
v_mvarId_1580_ = lean_ctor_get(v_goal_1566_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_goal_1566_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1582_ = v_goal_1566_;
v_isShared_1583_ = v_isSharedCheck_1619_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_mvarId_1580_);
lean_inc(v_toGoalState_1579_);
lean_dec(v_goal_1566_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1619_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1580_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 1, v_a_1585_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_toGoalState_1579_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1585_);
v___x_1587_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v_scope_1565_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = lean_mk_empty_array_with_capacity(v___x_1589_);
v___x_1591_ = lean_array_push(v___x_1590_, v___x_1588_);
v___x_1592_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(v___x_1591_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1600_; 
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v___x_1592_, 0);
lean_dec(v_unused_1601_);
v___x_1594_ = v___x_1592_;
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v___x_1592_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = lean_box(0);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1592_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1592_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_del_object(v___x_1582_);
lean_dec_ref(v_toGoalState_1579_);
lean_dec_ref(v_scope_1565_);
v_a_1611_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1584_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1584_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1620_, lean_object* v_goal_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1620_, v_goal_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v_mvarId_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(v_mvarId_1635_, v___y_1644_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v_mvarId_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_mvarId_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_mvarId_1649_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_00_u03b2_1663_, lean_object* v_m_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_m_1664_, v_a_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_00_u03b2_1667_, lean_object* v_m_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_00_u03b2_1667_, v_m_1668_, v_a_1669_);
lean_dec(v_a_1669_);
lean_dec_ref(v_m_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3(lean_object* v_00_u03b2_1671_, lean_object* v_m_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(v_m_1672_, v_a_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___boxed(lean_object* v_00_u03b2_1675_, lean_object* v_m_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3(v_00_u03b2_1675_, v_m_1676_, v_a_1677_);
lean_dec(v_a_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4(lean_object* v_inst_1679_, lean_object* v_a_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(v_a_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___boxed(lean_object* v_inst_1694_, lean_object* v_a_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4(v_inst_1694_, v_a_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2(lean_object* v_00_u03b2_1709_, lean_object* v_a_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(v_a_1710_, v_x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1713_, lean_object* v_a_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2(v_00_u03b2_1713_, v_a_1714_, v_x_1715_);
lean_dec(v_x_1715_);
lean_dec(v_a_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4(lean_object* v_00_u03b2_1717_, lean_object* v_a_1718_, lean_object* v_x_1719_){
_start:
{
uint8_t v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(v_a_1718_, v_x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1721_, lean_object* v_a_1722_, lean_object* v_x_1723_){
_start:
{
uint8_t v_res_1724_; lean_object* v_r_1725_; 
v_res_1724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4(v_00_u03b2_1721_, v_a_1722_, v_x_1723_);
lean_dec(v_x_1723_);
lean_dec(v_a_1722_);
v_r_1725_ = lean_box(v_res_1724_);
return v_r_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5(lean_object* v_00_u03b2_1726_, lean_object* v_a_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1727_, v_x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1730_, lean_object* v_a_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5(v_00_u03b2_1730_, v_a_1731_, v_x_1732_);
lean_dec(v_a_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_config_1745_; lean_object* v_sharedExprs_1746_; uint8_t v_verbose_1747_; uint8_t v_enforceUnfoldReducible_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_config_1745_ = lean_ctor_get(v___y_1738_, 1);
v_sharedExprs_1746_ = lean_ctor_get(v___y_1738_, 0);
v_verbose_1747_ = lean_ctor_get_uint8(v_config_1745_, 0);
v_enforceUnfoldReducible_1748_ = lean_ctor_get_uint8(v_config_1745_, 1);
v___x_1749_ = 0;
v___x_1750_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_1750_, 0, v_verbose_1747_);
lean_ctor_set_uint8(v___x_1750_, 1, v_enforceUnfoldReducible_1748_);
lean_ctor_set_uint8(v___x_1750_, 2, v___x_1749_);
lean_inc_ref(v_sharedExprs_1746_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_sharedExprs_1746_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1741_);
lean_inc_ref(v___y_1740_);
lean_inc(v___y_1739_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
lean_inc(v___y_1735_);
v___x_1752_ = lean_apply_10(v_x_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___x_1751_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_1778_, v_x_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_1791_, lean_object* v_scope_1792_, lean_object* v_goal_1793_, lean_object* v_ctx_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_st_mk_ref(v_initState_1791_);
v___x_1806_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1792_, v_goal_1793_, v_ctx_1794_, v___x_1805_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_st_ref_get(v___x_1805_);
lean_dec(v___x_1805_);
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v_a_1807_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v___x_1805_);
v_a_1817_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1806_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1806_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_1825_, lean_object* v_scope_1826_, lean_object* v_goal_1827_, lean_object* v_ctx_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_1825_, v_scope_1826_, v_goal_1827_, v_ctx_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v_ctx_1828_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v_mctx_1844_; lean_object* v_eAssignment_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1843_ = lean_st_ref_get(v___y_1841_);
v_mctx_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_mctx_1844_);
lean_dec(v___x_1843_);
v_eAssignment_1845_ = lean_ctor_get(v_mctx_1844_, 8);
lean_inc_ref(v_eAssignment_1845_);
lean_dec_ref(v_mctx_1844_);
v___x_1846_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1845_, v_mvarId_1840_);
lean_dec_ref(v_eAssignment_1845_);
v___x_1847_ = lean_box(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec(v_mvarId_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_1853_, size_t v_i_1854_, size_t v_stop_1855_, lean_object* v_b_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_a_1868_; uint8_t v___x_1872_; 
v___x_1872_ = lean_usize_dec_eq(v_i_1854_, v_stop_1855_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v_mvarId_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_array_uget_borrowed(v_as_1853_, v_i_1854_);
v_mvarId_1874_ = lean_ctor_get(v___x_1873_, 1);
v___x_1875_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_1874_, v___y_1863_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; uint8_t v___x_1877_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1877_ = lean_unbox(v_a_1876_);
lean_dec(v_a_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
lean_inc(v___x_1873_);
v___x_1878_ = lean_array_push(v_b_1856_, v___x_1873_);
v_a_1868_ = v___x_1878_;
goto v___jp_1867_;
}
else
{
v_a_1868_ = v_b_1856_;
goto v___jp_1867_;
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_b_1856_);
v_a_1879_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1875_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1875_);
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
else
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_b_1856_);
return v___x_1887_;
}
v___jp_1867_:
{
size_t v___x_1869_; size_t v___x_1870_; 
v___x_1869_ = ((size_t)1ULL);
v___x_1870_ = lean_usize_add(v_i_1854_, v___x_1869_);
v_i_1854_ = v___x_1870_;
v_b_1856_ = v_a_1868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_1888_, lean_object* v_i_1889_, lean_object* v_stop_1890_, lean_object* v_b_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
size_t v_i_boxed_1902_; size_t v_stop_boxed_1903_; lean_object* v_res_1904_; 
v_i_boxed_1902_ = lean_unbox_usize(v_i_1889_);
lean_dec(v_i_1889_);
v_stop_boxed_1903_ = lean_unbox_usize(v_stop_1890_);
lean_dec(v_stop_1890_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_1888_, v_i_boxed_1902_, v_stop_boxed_1903_, v_b_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v_as_1888_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_1906_, size_t v_i_1907_, lean_object* v_bs_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_bs_1908_);
return v___x_1915_;
}
else
{
lean_object* v_v_1916_; lean_object* v_mvarId_1917_; lean_object* v___x_1918_; lean_object* v_bs_x27_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_v_1916_ = lean_array_uget_borrowed(v_bs_1908_, v_i_1907_);
v_mvarId_1917_ = lean_ctor_get(v_v_1916_, 1);
lean_inc_n(v_mvarId_1917_, 2);
v___x_1918_ = lean_unsigned_to_nat(0u);
v_bs_x27_1919_ = lean_array_uset(v_bs_1908_, v_i_1907_, v___x_1918_);
v___x_1920_ = lean_usize_to_nat(v_i_1907_);
v___x_1921_ = l_Lean_MVarId_getTag(v_mvarId_1917_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_add(v___x_1920_, v___x_1924_);
lean_dec(v___x_1920_);
v___x_1926_ = l_Nat_reprFast(v___x_1925_);
v___x_1927_ = lean_string_append(v___x_1923_, v___x_1926_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = lean_box(0);
v___x_1929_ = l_Lean_Name_str___override(v___x_1928_, v___x_1927_);
v___x_1930_ = l_Lean_Name_eraseMacroScopes(v_a_1922_);
lean_dec(v_a_1922_);
v___x_1931_ = l_Lean_Name_append(v___x_1929_, v___x_1930_);
v___x_1932_ = l_Lean_MVarId_setTag___redArg(v_mvarId_1917_, v___x_1931_, v___y_1910_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1907_, v___x_1934_);
v___x_1936_ = lean_array_uset(v_bs_x27_1919_, v_i_1907_, v_a_1933_);
v_i_1907_ = v___x_1935_;
v_bs_1908_ = v___x_1936_;
goto _start;
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_bs_x27_1919_);
v_a_1938_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1932_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1932_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v___x_1920_);
lean_dec_ref(v_bs_x27_1919_);
lean_dec(v_mvarId_1917_);
v_a_1946_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1921_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1921_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_bs_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
size_t v_sz_boxed_1962_; size_t v_i_boxed_1963_; lean_object* v_res_1964_; 
v_sz_boxed_1962_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1963_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_1962_, v_i_boxed_1963_, v_bs_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_1966_, size_t v_i_1967_, lean_object* v_bs_1968_, lean_object* v___y_1969_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_usize_dec_lt(v_i_1967_, v_sz_1966_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_bs_1968_);
return v___x_1972_;
}
else
{
lean_object* v_v_1973_; lean_object* v___x_1974_; lean_object* v_bs_x27_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_v_1973_ = lean_array_uget(v_bs_1968_, v_i_1967_);
v___x_1974_ = lean_unsigned_to_nat(0u);
v_bs_x27_1975_ = lean_array_uset(v_bs_1968_, v_i_1967_, v___x_1974_);
v___x_1976_ = lean_usize_to_nat(v_i_1967_);
v___x_1977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v___x_1976_, v___x_1978_);
lean_dec(v___x_1976_);
v___x_1980_ = l_Nat_reprFast(v___x_1979_);
v___x_1981_ = lean_string_append(v___x_1977_, v___x_1980_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = lean_box(0);
v___x_1983_ = l_Lean_Name_str___override(v___x_1982_, v___x_1981_);
v___x_1984_ = l_Lean_MVarId_setTag___redArg(v_v_1973_, v___x_1983_, v___y_1969_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; size_t v___x_1986_; size_t v___x_1987_; lean_object* v___x_1988_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1967_, v___x_1986_);
v___x_1988_ = lean_array_uset(v_bs_x27_1975_, v_i_1967_, v_a_1985_);
v_i_1967_ = v___x_1987_;
v_bs_1968_ = v___x_1988_;
goto _start;
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v_bs_x27_1975_);
v_a_1990_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1984_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1984_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_1998_, lean_object* v_i_1999_, lean_object* v_bs_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
size_t v_sz_boxed_2003_; size_t v_i_boxed_2004_; lean_object* v_res_2005_; 
v_sz_boxed_2003_ = lean_unbox_usize(v_sz_1998_);
lean_dec(v_sz_1998_);
v_i_boxed_2004_ = lean_unbox_usize(v_i_1999_);
lean_dec(v_i_1999_);
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_2003_, v_i_boxed_2004_, v_bs_2000_, v___y_2001_);
lean_dec(v___y_2001_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_2006_, size_t v_i_2007_, size_t v_stop_2008_, lean_object* v_b_2009_){
_start:
{
lean_object* v___y_2011_; uint8_t v___x_2015_; 
v___x_2015_ = lean_usize_dec_eq(v_i_2007_, v_stop_2008_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; uint8_t v_retired_2017_; 
v___x_2016_ = lean_array_uget_borrowed(v_as_2006_, v_i_2007_);
v_retired_2017_ = lean_ctor_get_uint8(v___x_2016_, sizeof(void*)*4);
if (v_retired_2017_ == 0)
{
lean_object* v_frameStx_2018_; lean_object* v___x_2019_; 
v_frameStx_2018_ = lean_ctor_get(v___x_2016_, 2);
lean_inc(v_frameStx_2018_);
v___x_2019_ = lean_array_push(v_b_2009_, v_frameStx_2018_);
v___y_2011_ = v___x_2019_;
goto v___jp_2010_;
}
else
{
v___y_2011_ = v_b_2009_;
goto v___jp_2010_;
}
}
else
{
return v_b_2009_;
}
v___jp_2010_:
{
size_t v___x_2012_; size_t v___x_2013_; 
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_2007_, v___x_2012_);
v_i_2007_ = v___x_2013_;
v_b_2009_ = v___y_2011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_2020_, lean_object* v_i_2021_, lean_object* v_stop_2022_, lean_object* v_b_2023_){
_start:
{
size_t v_i_boxed_2024_; size_t v_stop_boxed_2025_; lean_object* v_res_2026_; 
v_i_boxed_2024_ = lean_unbox_usize(v_i_2021_);
lean_dec(v_i_2021_);
v_stop_boxed_2025_ = lean_unbox_usize(v_stop_2022_);
lean_dec(v_stop_2022_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2020_, v_i_boxed_2024_, v_stop_boxed_2025_, v_b_2023_);
lean_dec_ref(v_as_2020_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_2029_, lean_object* v_start_2030_, lean_object* v_stop_2031_){
_start:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0));
v___x_2033_ = lean_nat_dec_lt(v_start_2030_, v_stop_2031_);
if (v___x_2033_ == 0)
{
return v___x_2032_;
}
else
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = lean_array_get_size(v_as_2029_);
v___x_2035_ = lean_nat_dec_le(v_stop_2031_, v___x_2034_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; 
v___x_2036_ = lean_nat_dec_lt(v_start_2030_, v___x_2034_);
if (v___x_2036_ == 0)
{
return v___x_2032_;
}
else
{
size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_usize_of_nat(v_start_2030_);
v___x_2038_ = lean_usize_of_nat(v___x_2034_);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2029_, v___x_2037_, v___x_2038_, v___x_2032_);
return v___x_2039_;
}
}
else
{
size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_usize_of_nat(v_start_2030_);
v___x_2041_ = lean_usize_of_nat(v_stop_2031_);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2029_, v___x_2040_, v___x_2041_, v___x_2032_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_2043_, lean_object* v_start_2044_, lean_object* v_stop_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_2043_, v_start_2044_, v_stop_2045_);
lean_dec(v_stop_2045_);
lean_dec(v_start_2044_);
lean_dec_ref(v_as_2043_);
return v_res_2046_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = lean_unsigned_to_nat(16u);
v___x_2049_ = lean_mk_array(v___x_2048_, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___x_2050_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2056_);
lean_ctor_set(v___x_2058_, 2, v___x_2056_);
lean_ctor_set(v___x_2058_, 3, v___x_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_2059_, lean_object* v_ctx_2060_, lean_object* v_scope_2061_, lean_object* v_stepLimit_x3f_2062_, lean_object* v_frameDB_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___x_2074_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v_a_2079_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___y_2089_; 
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2085_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_2086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_2087_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_2062_) == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_box(1);
v___y_2089_ = v___x_2141_;
goto v___jp_2088_;
}
else
{
lean_object* v_val_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
v_val_2142_ = lean_ctor_get(v_stepLimit_x3f_2062_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_stepLimit_x3f_2062_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v_stepLimit_x3f_2062_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_val_2142_);
lean_dec(v_stepLimit_x3f_2062_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 0);
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_val_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v___y_2089_ = v___x_2147_;
goto v___jp_2088_;
}
}
}
v___jp_2075_:
{
lean_object* v_entries_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_entries_2080_ = lean_ctor_get(v___y_2076_, 1);
lean_inc_ref(v_entries_2080_);
lean_dec_ref(v___y_2076_);
v___x_2081_ = lean_array_get_size(v_entries_2080_);
v___x_2082_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_2080_, v___x_2074_, v___x_2081_);
lean_dec_ref(v_entries_2080_);
v___x_2083_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2083_, 0, v___y_2078_);
lean_ctor_set(v___x_2083_, 1, v_a_2079_);
lean_ctor_set(v___x_2083_, 2, v___y_2077_);
lean_ctor_set(v___x_2083_, 3, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
v___jp_2088_:
{
lean_object* v_initState_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; 
v_initState_2090_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_initState_2090_, 0, v___x_2085_);
lean_ctor_set(v_initState_2090_, 1, v___x_2085_);
lean_ctor_set(v_initState_2090_, 2, v___x_2085_);
lean_ctor_set(v_initState_2090_, 3, v___x_2085_);
lean_ctor_set(v_initState_2090_, 4, v_frameDB_2063_);
lean_ctor_set(v_initState_2090_, 5, v___x_2086_);
lean_ctor_set(v_initState_2090_, 6, v___x_2086_);
lean_ctor_set(v_initState_2090_, 7, v___x_2087_);
lean_ctor_set(v_initState_2090_, 8, v___y_2089_);
lean_ctor_set(v_initState_2090_, 9, v___x_2085_);
lean_ctor_set(v_initState_2090_, 10, v___x_2085_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2091_, 0, v_initState_2090_);
lean_closure_set(v___f_2091_, 1, v_scope_2061_);
lean_closure_set(v___f_2091_, 2, v_goal_2059_);
lean_closure_set(v___f_2091_, 3, v_ctx_2060_);
v___x_2092_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_2091_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v_snd_2094_; lean_object* v_frameDB_2095_; lean_object* v_invariants_2096_; lean_object* v_vcs_2097_; lean_object* v_inlineHandledInvariants_2098_; size_t v_sz_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v_snd_2094_ = lean_ctor_get(v_a_2093_, 1);
lean_inc(v_snd_2094_);
lean_dec(v_a_2093_);
v_frameDB_2095_ = lean_ctor_get(v_snd_2094_, 4);
lean_inc_ref(v_frameDB_2095_);
v_invariants_2096_ = lean_ctor_get(v_snd_2094_, 5);
lean_inc_ref_n(v_invariants_2096_, 2);
v_vcs_2097_ = lean_ctor_get(v_snd_2094_, 6);
lean_inc_ref(v_vcs_2097_);
v_inlineHandledInvariants_2098_ = lean_ctor_get(v_snd_2094_, 9);
lean_inc_ref(v_inlineHandledInvariants_2098_);
lean_dec(v_snd_2094_);
v_sz_2099_ = lean_array_size(v_invariants_2096_);
v___x_2100_ = ((size_t)0ULL);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_2099_, v___x_2100_, v_invariants_2096_, v_a_2070_);
if (lean_obj_tag(v___x_2101_) == 0)
{
size_t v_sz_2102_; lean_object* v___x_2103_; 
lean_dec_ref_known(v___x_2101_, 1);
v_sz_2102_ = lean_array_size(v_vcs_2097_);
lean_inc_ref(v_vcs_2097_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2102_, v___x_2100_, v_vcs_2097_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_dec_ref_known(v___x_2103_, 1);
v___x_2104_ = lean_array_get_size(v_vcs_2097_);
v___x_2105_ = lean_nat_dec_lt(v___x_2074_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_dec_ref(v_vcs_2097_);
v___y_2076_ = v_frameDB_2095_;
v___y_2077_ = v_inlineHandledInvariants_2098_;
v___y_2078_ = v_invariants_2096_;
v_a_2079_ = v___x_2086_;
goto v___jp_2075_;
}
else
{
size_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_usize_of_nat(v___x_2104_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_2097_, v___x_2100_, v___x_2106_, v___x_2086_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec_ref(v_vcs_2097_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___y_2076_ = v_frameDB_2095_;
v___y_2077_ = v_inlineHandledInvariants_2098_;
v___y_2078_ = v_invariants_2096_;
v_a_2079_ = v_a_2108_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_inlineHandledInvariants_2098_);
lean_dec_ref(v_invariants_2096_);
lean_dec_ref(v_frameDB_2095_);
v_a_2109_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2107_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_inlineHandledInvariants_2098_);
lean_dec_ref(v_vcs_2097_);
lean_dec_ref(v_invariants_2096_);
lean_dec_ref(v_frameDB_2095_);
v_a_2117_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2103_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2103_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_inlineHandledInvariants_2098_);
lean_dec_ref(v_vcs_2097_);
lean_dec_ref(v_invariants_2096_);
lean_dec_ref(v_frameDB_2095_);
v_a_2125_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2101_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2101_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v_a_2133_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2092_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2092_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_2150_, lean_object* v_ctx_2151_, lean_object* v_scope_2152_, lean_object* v_stepLimit_x3f_2153_, lean_object* v_frameDB_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_2150_, v_ctx_2151_, v_scope_2152_, v_stepLimit_x3f_2153_, v_frameDB_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2166_, v___y_2173_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec(v_mvarId_2178_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_2190_, size_t v_sz_2191_, size_t v_i_2192_, lean_object* v_bs_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_2191_, v_i_2192_, v_bs_2193_, v___y_2200_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_2205_, lean_object* v_sz_2206_, lean_object* v_i_2207_, lean_object* v_bs_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
size_t v_sz_boxed_2219_; size_t v_i_boxed_2220_; lean_object* v_res_2221_; 
v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2206_);
lean_dec(v_sz_2206_);
v_i_boxed_2220_ = lean_unbox_usize(v_i_2207_);
lean_dec(v_i_2207_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_2205_, v_sz_boxed_2219_, v_i_boxed_2220_, v_bs_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v_as_2205_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_2222_, size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_bs_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2223_, v_i_2224_, v_bs_2225_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_2237_, lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_bs_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
size_t v_sz_boxed_2251_; size_t v_i_boxed_2252_; lean_object* v_res_2253_; 
v_sz_boxed_2251_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2252_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_2237_, v_sz_boxed_2251_, v_i_boxed_2252_, v_bs_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v_as_2237_);
return v_res_2253_;
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
