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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0(lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; 
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1094_ = lean_apply_12(v_x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, lean_box(0));
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0___boxed(lean_object* v_x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0(v_x_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(lean_object* v_mvarId_1109_, lean_object* v_x_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
lean_inc(v___y_1113_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
v___f_1123_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1123_, 0, v_x_1110_);
lean_closure_set(v___f_1123_, 1, v___y_1111_);
lean_closure_set(v___f_1123_, 2, v___y_1112_);
lean_closure_set(v___f_1123_, 3, v___y_1113_);
lean_closure_set(v___f_1123_, 4, v___y_1114_);
lean_closure_set(v___f_1123_, 5, v___y_1115_);
lean_closure_set(v___f_1123_, 6, v___y_1116_);
lean_closure_set(v___f_1123_, 7, v___y_1117_);
v___x_1124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1109_, v___f_1123_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
return v___x_1124_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___boxed(lean_object* v_mvarId_1133_, lean_object* v_x_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(v_mvarId_1133_, v_x_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0(lean_object* v_00_u03b1_1148_, lean_object* v_mvarId_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(v_mvarId_1149_, v_x_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_mvarId_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0(v_00_u03b1_1164_, v_mvarId_1165_, v_x_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0(lean_object* v_goal_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_simpMethods_1196_; 
v_simpMethods_1196_ = lean_ctor_get(v___y_1184_, 2);
if (lean_obj_tag(v_simpMethods_1196_) == 1)
{
lean_object* v_val_1197_; lean_object* v___x_1198_; 
v_val_1197_ = lean_ctor_get(v_simpMethods_1196_, 0);
lean_inc(v_goal_1183_);
v___x_1198_ = l_Lean_MVarId_getType(v_goal_1183_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v_simpState_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = lean_st_ref_get(v___y_1185_);
v_simpState_1201_ = lean_ctor_get(v___x_1200_, 7);
lean_inc_ref(v_simpState_1201_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1202_, 0, v_a_1199_);
v___x_1203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___closed__0));
lean_inc(v_val_1197_);
v___x_1204_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_1202_, v_val_1197_, v___x_1203_, v_simpState_1201_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1208_; lean_object* v_specBackwardRuleCache_1209_; lean_object* v_splitBackwardRuleCache_1210_; lean_object* v_latticeBackwardRuleCache_1211_; lean_object* v_frameBackwardRuleCache_1212_; lean_object* v_frameDB_1213_; lean_object* v_invariants_1214_; lean_object* v_vcs_1215_; lean_object* v_fuel_1216_; lean_object* v_inlineHandledInvariants_1217_; lean_object* v_pendingJoinPoints_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1227_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v_fst_1206_ = lean_ctor_get(v_a_1205_, 0);
lean_inc(v_fst_1206_);
v_snd_1207_ = lean_ctor_get(v_a_1205_, 1);
lean_inc(v_snd_1207_);
lean_dec(v_a_1205_);
v___x_1208_ = lean_st_ref_take(v___y_1185_);
v_specBackwardRuleCache_1209_ = lean_ctor_get(v___x_1208_, 0);
v_splitBackwardRuleCache_1210_ = lean_ctor_get(v___x_1208_, 1);
v_latticeBackwardRuleCache_1211_ = lean_ctor_get(v___x_1208_, 2);
v_frameBackwardRuleCache_1212_ = lean_ctor_get(v___x_1208_, 3);
v_frameDB_1213_ = lean_ctor_get(v___x_1208_, 4);
v_invariants_1214_ = lean_ctor_get(v___x_1208_, 5);
v_vcs_1215_ = lean_ctor_get(v___x_1208_, 6);
v_fuel_1216_ = lean_ctor_get(v___x_1208_, 8);
v_inlineHandledInvariants_1217_ = lean_ctor_get(v___x_1208_, 9);
v_pendingJoinPoints_1218_ = lean_ctor_get(v___x_1208_, 10);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v___x_1208_, 7);
lean_dec(v_unused_1228_);
v___x_1220_ = v___x_1208_;
v_isShared_1221_ = v_isSharedCheck_1227_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_pendingJoinPoints_1218_);
lean_inc(v_inlineHandledInvariants_1217_);
lean_inc(v_fuel_1216_);
lean_inc(v_vcs_1215_);
lean_inc(v_invariants_1214_);
lean_inc(v_frameDB_1213_);
lean_inc(v_frameBackwardRuleCache_1212_);
lean_inc(v_latticeBackwardRuleCache_1211_);
lean_inc(v_splitBackwardRuleCache_1210_);
lean_inc(v_specBackwardRuleCache_1209_);
lean_dec(v___x_1208_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1227_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 7, v_snd_1207_);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_specBackwardRuleCache_1209_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_splitBackwardRuleCache_1210_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_latticeBackwardRuleCache_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_frameBackwardRuleCache_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_frameDB_1213_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v_invariants_1214_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_vcs_1215_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v_snd_1207_);
lean_ctor_set(v_reuseFailAlloc_1226_, 8, v_fuel_1216_);
lean_ctor_set(v_reuseFailAlloc_1226_, 9, v_inlineHandledInvariants_1217_);
lean_ctor_set(v_reuseFailAlloc_1226_, 10, v_pendingJoinPoints_1218_);
v___x_1223_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_st_ref_put(v___y_1185_, v___x_1223_);
v___x_1225_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_1206_, v_goal_1183_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_goal_1183_);
v_a_1229_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1204_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1204_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_goal_1183_);
v_a_1237_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1198_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1198_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_goal_1183_);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___boxed(lean_object* v_goal_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0(v_goal_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(lean_object* v_goal_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; 
lean_inc(v_goal_1261_);
v___f_1274_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1274_, 0, v_goal_1261_);
v___x_1275_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(v_goal_1261_, v___f_1274_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___boxed(lean_object* v_goal_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(v_goal_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1290_, lean_object* v_reason_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_goal_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v_goal_1398_; lean_object* v_toGoalState_1399_; lean_object* v_mvarId_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v_toGoalState_1432_; lean_object* v_mvarId_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1485_; 
v_toGoalState_1432_ = lean_ctor_get(v_goal_1290_, 0);
v_mvarId_1433_ = lean_ctor_get(v_goal_1290_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_goal_1290_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1435_ = v_goal_1290_;
v_isShared_1436_ = v_isSharedCheck_1485_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_mvarId_1433_);
lean_inc(v_toGoalState_1432_);
lean_dec(v_goal_1290_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1485_;
goto v_resetjp_1434_;
}
v___jp_1304_:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1305_, v___y_1306_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1388_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1388_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1388_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_toGoalState_1322_; uint8_t v_inconsistent_1323_; 
v_toGoalState_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc_ref(v_toGoalState_1322_);
v_inconsistent_1323_ = lean_ctor_get_uint8(v_toGoalState_1322_, sizeof(void*)*20 + 8);
if (v_inconsistent_1323_ == 0)
{
lean_object* v_mvarId_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1382_; 
lean_del_object(v___x_1320_);
v_mvarId_1324_ = lean_ctor_get(v_a_1318_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_a_1318_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_a_1318_, 0);
lean_dec(v_unused_1383_);
v___x_1326_ = v_a_1318_;
v_isShared_1327_ = v_isSharedCheck_1382_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_mvarId_1324_);
lean_dec(v_a_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1382_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_mvarId_1324_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1373_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1373_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1373_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
if (lean_obj_tag(v_a_1329_) == 1)
{
lean_object* v_val_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; 
lean_del_object(v___x_1331_);
v_val_1333_ = lean_ctor_get(v_a_1329_, 0);
lean_inc_n(v_val_1333_, 2);
lean_dec_ref_known(v_a_1329_, 1);
v___x_1334_ = 2;
v___x_1335_ = l_Lean_MVarId_setKind___redArg(v_val_1333_, v___x_1334_, v___y_1314_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1335_, 0);
lean_dec(v_unused_1368_);
v___x_1337_ = v___x_1335_;
v_isShared_1338_ = v_isSharedCheck_1367_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v___x_1335_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1367_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v_specBackwardRuleCache_1340_; lean_object* v_splitBackwardRuleCache_1341_; lean_object* v_latticeBackwardRuleCache_1342_; lean_object* v_frameBackwardRuleCache_1343_; lean_object* v_frameDB_1344_; lean_object* v_invariants_1345_; lean_object* v_vcs_1346_; lean_object* v_simpState_1347_; lean_object* v_fuel_1348_; lean_object* v_inlineHandledInvariants_1349_; lean_object* v_pendingJoinPoints_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1366_; 
v___x_1339_ = lean_st_ref_take(v___y_1307_);
v_specBackwardRuleCache_1340_ = lean_ctor_get(v___x_1339_, 0);
v_splitBackwardRuleCache_1341_ = lean_ctor_get(v___x_1339_, 1);
v_latticeBackwardRuleCache_1342_ = lean_ctor_get(v___x_1339_, 2);
v_frameBackwardRuleCache_1343_ = lean_ctor_get(v___x_1339_, 3);
v_frameDB_1344_ = lean_ctor_get(v___x_1339_, 4);
v_invariants_1345_ = lean_ctor_get(v___x_1339_, 5);
v_vcs_1346_ = lean_ctor_get(v___x_1339_, 6);
v_simpState_1347_ = lean_ctor_get(v___x_1339_, 7);
v_fuel_1348_ = lean_ctor_get(v___x_1339_, 8);
v_inlineHandledInvariants_1349_ = lean_ctor_get(v___x_1339_, 9);
v_pendingJoinPoints_1350_ = lean_ctor_get(v___x_1339_, 10);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1352_ = v___x_1339_;
v_isShared_1353_ = v_isSharedCheck_1366_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_pendingJoinPoints_1350_);
lean_inc(v_inlineHandledInvariants_1349_);
lean_inc(v_fuel_1348_);
lean_inc(v_simpState_1347_);
lean_inc(v_vcs_1346_);
lean_inc(v_invariants_1345_);
lean_inc(v_frameDB_1344_);
lean_inc(v_frameBackwardRuleCache_1343_);
lean_inc(v_latticeBackwardRuleCache_1342_);
lean_inc(v_splitBackwardRuleCache_1341_);
lean_inc(v_specBackwardRuleCache_1340_);
lean_dec(v___x_1339_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1366_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_box(0);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_val_1333_);
v___x_1356_ = v___x_1326_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_toGoalState_1322_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_val_1333_);
v___x_1356_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_array_push(v_vcs_1346_, v___x_1356_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 6, v___x_1357_);
v___x_1359_ = v___x_1352_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_specBackwardRuleCache_1340_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_splitBackwardRuleCache_1341_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_latticeBackwardRuleCache_1342_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_frameBackwardRuleCache_1343_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_frameDB_1344_);
lean_ctor_set(v_reuseFailAlloc_1364_, 5, v_invariants_1345_);
lean_ctor_set(v_reuseFailAlloc_1364_, 6, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1364_, 7, v_simpState_1347_);
lean_ctor_set(v_reuseFailAlloc_1364_, 8, v_fuel_1348_);
lean_ctor_set(v_reuseFailAlloc_1364_, 9, v_inlineHandledInvariants_1349_);
lean_ctor_set(v_reuseFailAlloc_1364_, 10, v_pendingJoinPoints_1350_);
v___x_1359_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_st_ref_put(v___y_1307_, v___x_1359_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1354_);
v___x_1362_ = v___x_1337_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1354_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1333_);
lean_del_object(v___x_1326_);
lean_dec_ref(v_toGoalState_1322_);
return v___x_1335_;
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_dec(v_a_1329_);
lean_del_object(v___x_1326_);
lean_dec_ref(v_toGoalState_1322_);
v___x_1369_ = lean_box(0);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1369_);
v___x_1371_ = v___x_1331_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
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
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1326_);
lean_dec_ref(v_toGoalState_1322_);
v_a_1374_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1328_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1328_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_dec_ref(v_toGoalState_1322_);
lean_dec(v_a_1318_);
v___x_1384_ = lean_box(0);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1384_);
v___x_1386_ = v___x_1320_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
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
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1317_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1317_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
v___jp_1397_:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(v_mvarId_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1423_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1423_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1423_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
switch(lean_obj_tag(v_a_1413_))
{
case 0:
{
lean_del_object(v___x_1415_);
lean_dec_ref(v_toGoalState_1399_);
v_goal_1305_ = v_goal_1398_;
v___y_1306_ = v___y_1401_;
v___y_1307_ = v___y_1402_;
v___y_1308_ = v___y_1403_;
v___y_1309_ = v___y_1404_;
v___y_1310_ = v___y_1405_;
v___y_1311_ = v___y_1406_;
v___y_1312_ = v___y_1407_;
v___y_1313_ = v___y_1408_;
v___y_1314_ = v___y_1409_;
v___y_1315_ = v___y_1410_;
v___y_1316_ = v___y_1411_;
goto v___jp_1304_;
}
case 1:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec_ref(v_toGoalState_1399_);
lean_dec_ref(v_goal_1398_);
v___x_1417_ = lean_box(0);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
default: 
{
lean_object* v_mvarId_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1415_);
lean_dec_ref(v_goal_1398_);
v_mvarId_1421_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_mvarId_1421_);
lean_dec_ref_known(v_a_1413_, 1);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_toGoalState_1399_);
lean_ctor_set(v___x_1422_, 1, v_mvarId_1421_);
v_goal_1305_ = v___x_1422_;
v___y_1306_ = v___y_1401_;
v___y_1307_ = v___y_1402_;
v___y_1308_ = v___y_1403_;
v___y_1309_ = v___y_1404_;
v___y_1310_ = v___y_1405_;
v___y_1311_ = v___y_1406_;
v___y_1312_ = v___y_1407_;
v___y_1313_ = v___y_1408_;
v___y_1314_ = v___y_1409_;
v___y_1315_ = v___y_1410_;
v___y_1316_ = v___y_1411_;
goto v___jp_1304_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec_ref(v_toGoalState_1399_);
lean_dec_ref(v_goal_1398_);
v_a_1424_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1412_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1412_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1433_, v_a_1292_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_n(v_a_1438_, 2);
lean_dec_ref_known(v___x_1437_, 1);
lean_inc_ref(v_toGoalState_1432_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v_a_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_toGoalState_1432_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_a_1438_);
v___x_1440_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
switch(lean_obj_tag(v_reason_1291_))
{
case 2:
{
goto v___jp_1441_;
}
case 3:
{
goto v___jp_1441_;
}
default: 
{
lean_dec(v_a_1438_);
lean_dec_ref(v_toGoalState_1432_);
v_goal_1305_ = v___x_1440_;
v___y_1306_ = v_a_1292_;
v___y_1307_ = v_a_1293_;
v___y_1308_ = v_a_1294_;
v___y_1309_ = v_a_1295_;
v___y_1310_ = v_a_1296_;
v___y_1311_ = v_a_1297_;
v___y_1312_ = v_a_1298_;
v___y_1313_ = v_a_1299_;
v___y_1314_ = v_a_1300_;
v___y_1315_ = v_a_1301_;
v___y_1316_ = v_a_1302_;
goto v___jp_1304_;
}
}
v___jp_1441_:
{
lean_object* v___x_1442_; 
lean_inc(v_a_1438_);
v___x_1442_ = l_Lean_MVarId_getType(v_a_1438_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_n(v_a_1443_, 2);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_1443_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; size_t v___x_1446_; size_t v___x_1447_; uint8_t v___x_1448_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = lean_ptr_addr(v_a_1443_);
lean_dec(v_a_1443_);
v___x_1447_ = lean_ptr_addr(v_a_1445_);
v___x_1448_ = lean_usize_dec_eq(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref(v___x_1440_);
v___x_1449_ = l_Lean_MVarId_replaceTargetDefEqFast(v_a_1438_, v_a_1445_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_n(v_a_1450_, 2);
lean_dec_ref_known(v___x_1449_, 1);
lean_inc_ref(v_toGoalState_1432_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_toGoalState_1432_);
lean_ctor_set(v___x_1451_, 1, v_a_1450_);
v_goal_1398_ = v___x_1451_;
v_toGoalState_1399_ = v_toGoalState_1432_;
v_mvarId_1400_ = v_a_1450_;
v___y_1401_ = v_a_1292_;
v___y_1402_ = v_a_1293_;
v___y_1403_ = v_a_1294_;
v___y_1404_ = v_a_1295_;
v___y_1405_ = v_a_1296_;
v___y_1406_ = v_a_1297_;
v___y_1407_ = v_a_1298_;
v___y_1408_ = v_a_1299_;
v___y_1409_ = v_a_1300_;
v___y_1410_ = v_a_1301_;
v___y_1411_ = v_a_1302_;
goto v___jp_1397_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v_toGoalState_1432_);
v_a_1452_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1449_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1449_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_dec(v_a_1445_);
v_goal_1398_ = v___x_1440_;
v_toGoalState_1399_ = v_toGoalState_1432_;
v_mvarId_1400_ = v_a_1438_;
v___y_1401_ = v_a_1292_;
v___y_1402_ = v_a_1293_;
v___y_1403_ = v_a_1294_;
v___y_1404_ = v_a_1295_;
v___y_1405_ = v_a_1296_;
v___y_1406_ = v_a_1297_;
v___y_1407_ = v_a_1298_;
v___y_1408_ = v_a_1299_;
v___y_1409_ = v_a_1300_;
v___y_1410_ = v_a_1301_;
v___y_1411_ = v_a_1302_;
goto v___jp_1397_;
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1443_);
lean_dec_ref(v___x_1440_);
lean_dec(v_a_1438_);
lean_dec_ref(v_toGoalState_1432_);
v_a_1460_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1444_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1444_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___x_1440_);
lean_dec(v_a_1438_);
lean_dec_ref(v_toGoalState_1432_);
v_a_1468_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1442_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1442_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_del_object(v___x_1435_);
lean_dec_ref(v_toGoalState_1432_);
v_a_1477_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1437_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1437_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1486_, lean_object* v_reason_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1486_, v_reason_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_reason_1487_);
return v_res_1500_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(lean_object* v_a_1501_, lean_object* v_x_1502_){
_start:
{
if (lean_obj_tag(v_x_1502_) == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = 0;
return v___x_1503_;
}
else
{
lean_object* v_key_1504_; lean_object* v_tail_1505_; uint8_t v___x_1506_; 
v_key_1504_ = lean_ctor_get(v_x_1502_, 0);
v_tail_1505_ = lean_ctor_get(v_x_1502_, 2);
v___x_1506_ = l_Lean_instBEqMVarId_beq(v_key_1504_, v_a_1501_);
if (v___x_1506_ == 0)
{
v_x_1502_ = v_tail_1505_;
goto _start;
}
else
{
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg___boxed(lean_object* v_a_1508_, lean_object* v_x_1509_){
_start:
{
uint8_t v_res_1510_; lean_object* v_r_1511_; 
v_res_1510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(v_a_1508_, v_x_1509_);
lean_dec(v_x_1509_);
lean_dec(v_a_1508_);
v_r_1511_ = lean_box(v_res_1510_);
return v_r_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
if (lean_obj_tag(v_x_1513_) == 0)
{
return v_x_1513_;
}
else
{
lean_object* v_key_1514_; lean_object* v_value_1515_; lean_object* v_tail_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1525_; 
v_key_1514_ = lean_ctor_get(v_x_1513_, 0);
v_value_1515_ = lean_ctor_get(v_x_1513_, 1);
v_tail_1516_ = lean_ctor_get(v_x_1513_, 2);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_x_1513_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1518_ = v_x_1513_;
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_tail_1516_);
lean_inc(v_value_1515_);
lean_inc(v_key_1514_);
lean_dec(v_x_1513_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_instBEqMVarId_beq(v_key_1514_, v_a_1512_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1512_, v_tail_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 2, v___x_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_key_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_value_1515_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
else
{
lean_del_object(v___x_1518_);
lean_dec(v_value_1515_);
lean_dec(v_key_1514_);
return v_tail_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg___boxed(lean_object* v_a_1526_, lean_object* v_x_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1526_, v_x_1527_);
lean_dec(v_a_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(lean_object* v_m_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_size_1531_; lean_object* v_buckets_1532_; lean_object* v___x_1533_; uint64_t v___x_1534_; uint64_t v___x_1535_; uint64_t v___x_1536_; uint64_t v_fold_1537_; uint64_t v___x_1538_; uint64_t v___x_1539_; uint64_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; size_t v___x_1545_; lean_object* v_bkt_1546_; uint8_t v___x_1547_; 
v_size_1531_ = lean_ctor_get(v_m_1529_, 0);
v_buckets_1532_ = lean_ctor_get(v_m_1529_, 1);
v___x_1533_ = lean_array_get_size(v_buckets_1532_);
v___x_1534_ = l_Lean_instHashableMVarId_hash(v_a_1530_);
v___x_1535_ = 32ULL;
v___x_1536_ = lean_uint64_shift_right(v___x_1534_, v___x_1535_);
v_fold_1537_ = lean_uint64_xor(v___x_1534_, v___x_1536_);
v___x_1538_ = 16ULL;
v___x_1539_ = lean_uint64_shift_right(v_fold_1537_, v___x_1538_);
v___x_1540_ = lean_uint64_xor(v_fold_1537_, v___x_1539_);
v___x_1541_ = lean_uint64_to_usize(v___x_1540_);
v___x_1542_ = lean_usize_of_nat(v___x_1533_);
v___x_1543_ = ((size_t)1ULL);
v___x_1544_ = lean_usize_sub(v___x_1542_, v___x_1543_);
v___x_1545_ = lean_usize_land(v___x_1541_, v___x_1544_);
v_bkt_1546_ = lean_array_uget_borrowed(v_buckets_1532_, v___x_1545_);
v___x_1547_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(v_a_1530_, v_bkt_1546_);
if (v___x_1547_ == 0)
{
return v_m_1529_;
}
else
{
lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1560_; 
lean_inc(v_bkt_1546_);
lean_inc_ref(v_buckets_1532_);
lean_inc(v_size_1531_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_m_1529_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1561_ = lean_ctor_get(v_m_1529_, 1);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_m_1529_, 0);
lean_dec(v_unused_1562_);
v___x_1549_ = v_m_1529_;
v_isShared_1550_ = v_isSharedCheck_1560_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v_m_1529_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1560_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v_buckets_x27_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1551_ = lean_box(0);
v_buckets_x27_1552_ = lean_array_uset(v_buckets_1532_, v___x_1545_, v___x_1551_);
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_sub(v_size_1531_, v___x_1553_);
lean_dec(v_size_1531_);
v___x_1555_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_1530_, v_bkt_1546_);
v___x_1556_ = lean_array_uset(v_buckets_x27_1552_, v___x_1545_, v___x_1555_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 1, v___x_1556_);
lean_ctor_set(v___x_1549_, 0, v___x_1554_);
v___x_1558_ = v___x_1549_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg___boxed(lean_object* v_m_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(v_m_1563_, v_a_1564_);
lean_dec(v_a_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(lean_object* v_mvarId_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v_mctx_1570_; lean_object* v_eAssignment_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1569_ = lean_st_ref_get(v___y_1567_);
v_mctx_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_ref(v_mctx_1570_);
lean_dec(v___x_1569_);
v_eAssignment_1571_ = lean_ctor_get(v_mctx_1570_, 8);
lean_inc_ref(v_eAssignment_1571_);
lean_dec_ref(v_mctx_1570_);
v___x_1572_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_1571_, v_mvarId_1566_);
lean_dec_ref(v_eAssignment_1571_);
v___x_1573_ = lean_box(v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg___boxed(lean_object* v_mvarId_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(v_mvarId_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec(v_mvarId_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_box(0);
return v___x_1581_;
}
else
{
lean_object* v_key_1582_; lean_object* v_value_1583_; lean_object* v_tail_1584_; uint8_t v___x_1585_; 
v_key_1582_ = lean_ctor_get(v_x_1580_, 0);
v_value_1583_ = lean_ctor_get(v_x_1580_, 1);
v_tail_1584_ = lean_ctor_get(v_x_1580_, 2);
v___x_1585_ = l_Lean_instBEqMVarId_beq(v_key_1582_, v_a_1579_);
if (v___x_1585_ == 0)
{
v_x_1580_ = v_tail_1584_;
goto _start;
}
else
{
lean_object* v___x_1587_; 
lean_inc(v_value_1583_);
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_value_1583_);
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg___boxed(lean_object* v_a_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(v_a_1588_, v_x_1589_);
lean_dec(v_x_1589_);
lean_dec(v_a_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_m_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_buckets_1593_; lean_object* v___x_1594_; uint64_t v___x_1595_; uint64_t v___x_1596_; uint64_t v___x_1597_; uint64_t v_fold_1598_; uint64_t v___x_1599_; uint64_t v___x_1600_; uint64_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_buckets_1593_ = lean_ctor_get(v_m_1591_, 1);
v___x_1594_ = lean_array_get_size(v_buckets_1593_);
v___x_1595_ = l_Lean_instHashableMVarId_hash(v_a_1592_);
v___x_1596_ = 32ULL;
v___x_1597_ = lean_uint64_shift_right(v___x_1595_, v___x_1596_);
v_fold_1598_ = lean_uint64_xor(v___x_1595_, v___x_1597_);
v___x_1599_ = 16ULL;
v___x_1600_ = lean_uint64_shift_right(v_fold_1598_, v___x_1599_);
v___x_1601_ = lean_uint64_xor(v_fold_1598_, v___x_1600_);
v___x_1602_ = lean_uint64_to_usize(v___x_1601_);
v___x_1603_ = lean_usize_of_nat(v___x_1594_);
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_sub(v___x_1603_, v___x_1604_);
v___x_1606_ = lean_usize_land(v___x_1602_, v___x_1605_);
v___x_1607_ = lean_array_uget_borrowed(v_buckets_1593_, v___x_1606_);
v___x_1608_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(v_a_1592_, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_m_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_m_1609_, v_a_1610_);
lean_dec(v_a_1610_);
lean_dec_ref(v_m_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v___x_1612_, lean_object* v_scope_1613_, size_t v_sz_1614_, size_t v_i_1615_, lean_object* v_bs_1616_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_usize_dec_lt(v_i_1615_, v_sz_1614_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v_scope_1613_);
lean_dec_ref(v___x_1612_);
return v_bs_1616_;
}
else
{
lean_object* v_v_1618_; lean_object* v___x_1619_; lean_object* v_bs_x27_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; size_t v___x_1623_; size_t v___x_1624_; lean_object* v___x_1625_; 
v_v_1618_ = lean_array_uget(v_bs_1616_, v_i_1615_);
v___x_1619_ = lean_unsigned_to_nat(0u);
v_bs_x27_1620_ = lean_array_uset(v_bs_1616_, v_i_1615_, v___x_1619_);
lean_inc_ref(v___x_1612_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1612_);
lean_ctor_set(v___x_1621_, 1, v_v_1618_);
lean_inc_ref(v_scope_1613_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v_scope_1613_);
v___x_1623_ = ((size_t)1ULL);
v___x_1624_ = lean_usize_add(v_i_1615_, v___x_1623_);
v___x_1625_ = lean_array_uset(v_bs_x27_1620_, v_i_1615_, v___x_1622_);
v_i_1615_ = v___x_1624_;
v_bs_1616_ = v___x_1625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v___x_1627_, lean_object* v_scope_1628_, lean_object* v_sz_1629_, lean_object* v_i_1630_, lean_object* v_bs_1631_){
_start:
{
size_t v_sz_boxed_1632_; size_t v_i_boxed_1633_; lean_object* v_res_1634_; 
v_sz_boxed_1632_ = lean_unbox_usize(v_sz_1629_);
lean_dec(v_sz_1629_);
v_i_boxed_1633_ = lean_unbox_usize(v_i_1630_);
lean_dec(v_i_1630_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v___x_1627_, v_scope_1628_, v_sz_boxed_1632_, v_i_boxed_1633_, v_bs_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(lean_object* v_goal_1635_, lean_object* v_scope_1636_, lean_object* v___x_1637_, lean_object* v_____r_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1635_, v___y_1639_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1723_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1723_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1723_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_toGoalState_1656_; uint8_t v_inconsistent_1657_; 
v_toGoalState_1656_ = lean_ctor_get(v_a_1652_, 0);
v_inconsistent_1657_ = lean_ctor_get_uint8(v_toGoalState_1656_, sizeof(void*)*20 + 8);
if (v_inconsistent_1657_ == 0)
{
lean_object* v_mvarId_1658_; lean_object* v___x_1659_; 
lean_del_object(v___x_1654_);
v_mvarId_1658_ = lean_ctor_get(v_a_1652_, 1);
lean_inc(v_mvarId_1658_);
v___x_1659_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1636_, v_mvarId_1658_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
if (lean_obj_tag(v_a_1660_) == 0)
{
lean_object* v_scope_1661_; lean_object* v_subgoals_1662_; lean_object* v___x_1663_; 
lean_inc_ref(v_toGoalState_1656_);
lean_dec(v_a_1652_);
v_scope_1661_ = lean_ctor_get(v_a_1660_, 0);
lean_inc_ref(v_scope_1661_);
v_subgoals_1662_ = lean_ctor_get(v_a_1660_, 1);
lean_inc(v_subgoals_1662_);
lean_dec_ref_known(v_a_1660_, 2);
v___x_1663_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1662_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v_subgoals_1662_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1677_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1677_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1677_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; size_t v_sz_1669_; size_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1668_ = l_Array_reverse___redArg(v_a_1664_);
v_sz_1669_ = lean_array_size(v___x_1668_);
v___x_1670_ = ((size_t)0ULL);
v___x_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_toGoalState_1656_, v_scope_1661_, v_sz_1669_, v___x_1670_, v___x_1668_);
v___x_1672_ = l_Array_append___redArg(v___x_1637_, v___x_1671_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1673_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v_scope_1661_);
lean_dec_ref(v_toGoalState_1656_);
lean_dec_ref(v___x_1637_);
v_a_1678_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1663_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1663_);
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
else
{
lean_object* v_reason_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1710_; 
v_reason_1686_ = lean_ctor_get(v_a_1660_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1688_ = v_a_1660_;
v_isShared_1689_ = v_isSharedCheck_1710_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_reason_1686_);
lean_dec(v_a_1660_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1710_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1652_, v_reason_1686_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v_reason_1686_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1700_; 
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v___x_1690_, 0);
lean_dec(v_unused_1701_);
v___x_1692_ = v___x_1690_;
v_isShared_1693_ = v_isSharedCheck_1700_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v___x_1690_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1700_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1637_);
v___x_1695_ = v___x_1688_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1637_);
v___x_1695_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1697_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1695_);
v___x_1697_ = v___x_1692_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_del_object(v___x_1688_);
lean_dec_ref(v___x_1637_);
v_a_1702_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1690_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1690_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1652_);
lean_dec_ref(v___x_1637_);
v_a_1711_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1659_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1659_);
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
else
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_dec(v_a_1652_);
lean_dec_ref(v_scope_1636_);
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1637_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1719_);
v___x_1721_ = v___x_1654_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v___x_1637_);
lean_dec_ref(v_scope_1636_);
v_a_1724_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1651_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1651_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0___boxed(lean_object* v_goal_1732_, lean_object* v_scope_1733_, lean_object* v___x_1734_, lean_object* v_____r_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(v_goal_1732_, v_scope_1733_, v___x_1734_, v_____r_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(lean_object* v_a_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___y_1763_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = lean_array_get_size(v_a_1749_);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_nat_sub(v___x_1783_, v___x_1784_);
v___x_1786_ = lean_nat_dec_lt(v___x_1785_, v___x_1783_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_a_1749_);
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; lean_object* v_goal_1789_; lean_object* v_scope_1790_; lean_object* v_mvarId_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1788_ = lean_array_fget_borrowed(v_a_1749_, v___x_1785_);
lean_dec(v___x_1785_);
v_goal_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc_ref(v_goal_1789_);
v_scope_1790_ = lean_ctor_get(v___x_1788_, 1);
lean_inc_ref(v_scope_1790_);
v_mvarId_1791_ = lean_ctor_get(v_goal_1789_, 1);
v___x_1792_ = lean_array_pop(v_a_1749_);
v___x_1793_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(v_mvarId_1791_, v___y_1758_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; uint8_t v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1795_ = lean_unbox(v_a_1794_);
lean_dec(v_a_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v_pendingJoinPoints_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_st_ref_get(v___y_1751_);
v_pendingJoinPoints_1797_ = lean_ctor_get(v___x_1796_, 10);
lean_inc_ref(v_pendingJoinPoints_1797_);
lean_dec(v___x_1796_);
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_pendingJoinPoints_1797_, v_mvarId_1791_);
lean_dec_ref(v_pendingJoinPoints_1797_);
if (lean_obj_tag(v___x_1798_) == 1)
{
lean_object* v_val_1799_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; lean_object* v___x_1802_; lean_object* v_specBackwardRuleCache_1803_; lean_object* v_splitBackwardRuleCache_1804_; lean_object* v_latticeBackwardRuleCache_1805_; lean_object* v_frameBackwardRuleCache_1806_; lean_object* v_frameDB_1807_; lean_object* v_invariants_1808_; lean_object* v_vcs_1809_; lean_object* v_simpState_1810_; lean_object* v_fuel_1811_; lean_object* v_inlineHandledInvariants_1812_; lean_object* v_pendingJoinPoints_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1833_; 
v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v_fst_1800_ = lean_ctor_get(v_val_1799_, 0);
lean_inc(v_fst_1800_);
v_snd_1801_ = lean_ctor_get(v_val_1799_, 1);
lean_inc(v_snd_1801_);
lean_dec(v_val_1799_);
v___x_1802_ = lean_st_ref_take(v___y_1751_);
v_specBackwardRuleCache_1803_ = lean_ctor_get(v___x_1802_, 0);
v_splitBackwardRuleCache_1804_ = lean_ctor_get(v___x_1802_, 1);
v_latticeBackwardRuleCache_1805_ = lean_ctor_get(v___x_1802_, 2);
v_frameBackwardRuleCache_1806_ = lean_ctor_get(v___x_1802_, 3);
v_frameDB_1807_ = lean_ctor_get(v___x_1802_, 4);
v_invariants_1808_ = lean_ctor_get(v___x_1802_, 5);
v_vcs_1809_ = lean_ctor_get(v___x_1802_, 6);
v_simpState_1810_ = lean_ctor_get(v___x_1802_, 7);
v_fuel_1811_ = lean_ctor_get(v___x_1802_, 8);
v_inlineHandledInvariants_1812_ = lean_ctor_get(v___x_1802_, 9);
v_pendingJoinPoints_1813_ = lean_ctor_get(v___x_1802_, 10);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1815_ = v___x_1802_;
v_isShared_1816_ = v_isSharedCheck_1833_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_pendingJoinPoints_1813_);
lean_inc(v_inlineHandledInvariants_1812_);
lean_inc(v_fuel_1811_);
lean_inc(v_simpState_1810_);
lean_inc(v_vcs_1809_);
lean_inc(v_invariants_1808_);
lean_inc(v_frameDB_1807_);
lean_inc(v_frameBackwardRuleCache_1806_);
lean_inc(v_latticeBackwardRuleCache_1805_);
lean_inc(v_splitBackwardRuleCache_1804_);
lean_inc(v_specBackwardRuleCache_1803_);
lean_dec(v___x_1802_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1833_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(v_pendingJoinPoints_1813_, v_mvarId_1791_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 10, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_specBackwardRuleCache_1803_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_splitBackwardRuleCache_1804_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_latticeBackwardRuleCache_1805_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_frameBackwardRuleCache_1806_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_frameDB_1807_);
lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_invariants_1808_);
lean_ctor_set(v_reuseFailAlloc_1832_, 6, v_vcs_1809_);
lean_ctor_set(v_reuseFailAlloc_1832_, 7, v_simpState_1810_);
lean_ctor_set(v_reuseFailAlloc_1832_, 8, v_fuel_1811_);
lean_ctor_set(v_reuseFailAlloc_1832_, 9, v_inlineHandledInvariants_1812_);
lean_ctor_set(v_reuseFailAlloc_1832_, 10, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_st_ref_put(v___y_1751_, v___x_1819_);
v___x_1821_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_fst_1800_, v_snd_1801_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(v_goal_1789_, v_scope_1790_, v___x_1792_, v_a_1822_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
v___y_1763_ = v___x_1823_;
goto v___jp_1762_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec_ref(v___x_1792_);
lean_dec_ref(v_scope_1790_);
lean_dec_ref(v_goal_1789_);
v_a_1824_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1821_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1821_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec(v___x_1798_);
v___x_1834_ = lean_box(0);
v___x_1835_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___lam__0(v_goal_1789_, v_scope_1790_, v___x_1792_, v___x_1834_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
v___y_1763_ = v___x_1835_;
goto v___jp_1762_;
}
}
else
{
lean_dec_ref(v_scope_1790_);
lean_dec_ref(v_goal_1789_);
v_a_1749_ = v___x_1792_;
goto _start;
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v___x_1792_);
lean_dec_ref(v_scope_1790_);
lean_dec_ref(v_goal_1789_);
v_a_1837_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1793_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1793_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
v___jp_1762_:
{
if (lean_obj_tag(v___y_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1774_; 
v_a_1764_ = lean_ctor_get(v___y_1763_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___y_1763_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1766_ = v___y_1763_;
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___y_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
if (lean_obj_tag(v_a_1764_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; 
v_a_1768_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v_a_1764_, 1);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v_a_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
else
{
lean_object* v_a_1772_; 
lean_del_object(v___x_1766_);
v_a_1772_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v_a_1764_, 1);
v_a_1749_ = v_a_1772_;
goto _start;
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_a_1775_ = lean_ctor_get(v___y_1763_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___y_1763_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___y_1763_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___y_1763_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg___boxed(lean_object* v_a_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(v_a_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1859_, lean_object* v_goal_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_toGoalState_1873_; lean_object* v_mvarId_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1913_; 
v_toGoalState_1873_ = lean_ctor_get(v_goal_1860_, 0);
v_mvarId_1874_ = lean_ctor_get(v_goal_1860_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_goal_1860_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1876_ = v_goal_1860_;
v_isShared_1877_ = v_isSharedCheck_1913_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_mvarId_1874_);
lean_inc(v_toGoalState_1873_);
lean_dec(v_goal_1860_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1913_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1874_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_a_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_toGoalState_1873_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_a_1879_);
v___x_1881_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_scope_1859_);
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = lean_mk_empty_array_with_capacity(v___x_1883_);
v___x_1885_ = lean_array_push(v___x_1884_, v___x_1882_);
v___x_1886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(v___x_1885_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1894_; 
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1895_);
v___x_1888_ = v___x_1886_;
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1886_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1894_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1886_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_del_object(v___x_1876_);
lean_dec_ref(v_toGoalState_1873_);
lean_dec_ref(v_scope_1859_);
v_a_1905_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1878_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1878_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1914_, lean_object* v_goal_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1914_, v_goal_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v_mvarId_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___redArg(v_mvarId_1929_, v___y_1938_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v_mvarId_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_mvarId_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v_mvarId_1943_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_00_u03b2_1957_, lean_object* v_m_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_m_1958_, v_a_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_00_u03b2_1961_, lean_object* v_m_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_00_u03b2_1961_, v_m_1962_, v_a_1963_);
lean_dec(v_a_1963_);
lean_dec_ref(v_m_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3(lean_object* v_00_u03b2_1965_, lean_object* v_m_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___redArg(v_m_1966_, v_a_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3___boxed(lean_object* v_00_u03b2_1969_, lean_object* v_m_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3(v_00_u03b2_1969_, v_m_1970_, v_a_1971_);
lean_dec(v_a_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4(lean_object* v_inst_1973_, lean_object* v_a_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___redArg(v_a_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4___boxed(lean_object* v_inst_1988_, lean_object* v_a_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__4(v_inst_1988_, v_a_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2(lean_object* v_00_u03b2_2003_, lean_object* v_a_2004_, lean_object* v_x_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___redArg(v_a_2004_, v_x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2___boxed(lean_object* v_00_u03b2_2007_, lean_object* v_a_2008_, lean_object* v_x_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_work_spec__2_spec__2(v_00_u03b2_2007_, v_a_2008_, v_x_2009_);
lean_dec(v_x_2009_);
lean_dec(v_a_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4(lean_object* v_00_u03b2_2011_, lean_object* v_a_2012_, lean_object* v_x_2013_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___redArg(v_a_2012_, v_x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2015_, lean_object* v_a_2016_, lean_object* v_x_2017_){
_start:
{
uint8_t v_res_2018_; lean_object* v_r_2019_; 
v_res_2018_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__4(v_00_u03b2_2015_, v_a_2016_, v_x_2017_);
lean_dec(v_x_2017_);
lean_dec(v_a_2016_);
v_r_2019_ = lean_box(v_res_2018_);
return v_r_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5(lean_object* v_00_u03b2_2020_, lean_object* v_a_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___redArg(v_a_2021_, v_x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2024_, lean_object* v_a_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_VCGen_work_spec__3_spec__5(v_00_u03b2_2024_, v_a_2025_, v_x_2026_);
lean_dec(v_a_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_config_2039_; lean_object* v_sharedExprs_2040_; uint8_t v_verbose_2041_; uint8_t v_enforceUnfoldReducible_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_config_2039_ = lean_ctor_get(v___y_2032_, 1);
v_sharedExprs_2040_ = lean_ctor_get(v___y_2032_, 0);
v_verbose_2041_ = lean_ctor_get_uint8(v_config_2039_, 0);
v_enforceUnfoldReducible_2042_ = lean_ctor_get_uint8(v_config_2039_, 1);
v___x_2043_ = 0;
v___x_2044_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_2044_, 0, v_verbose_2041_);
lean_ctor_set_uint8(v___x_2044_, 1, v_enforceUnfoldReducible_2042_);
lean_ctor_set_uint8(v___x_2044_, 2, v___x_2043_);
lean_inc_ref(v_sharedExprs_2040_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_sharedExprs_2040_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc(v___y_2031_);
lean_inc_ref(v___y_2030_);
lean_inc(v___y_2029_);
v___x_2046_ = lean_apply_10(v_x_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___x_2045_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, lean_box(0));
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_2059_, lean_object* v_x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_x_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_2072_, v_x_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_2085_, lean_object* v_scope_2086_, lean_object* v_goal_2087_, lean_object* v_ctx_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_st_mk_ref(v_initState_2085_);
v___x_2100_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_2086_, v_goal_2087_, v_ctx_2088_, v___x_2099_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2110_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2110_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2110_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2105_ = lean_st_ref_get(v___x_2099_);
lean_dec(v___x_2099_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2101_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2106_);
v___x_2108_ = v___x_2103_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v___x_2099_);
v_a_2111_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2100_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2100_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_2119_, lean_object* v_scope_2120_, lean_object* v_goal_2121_, lean_object* v_ctx_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_2119_, v_scope_2120_, v_goal_2121_, v_ctx_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v_ctx_2122_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v_mctx_2138_; lean_object* v_eAssignment_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2137_ = lean_st_ref_get(v___y_2135_);
v_mctx_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_ref(v_mctx_2138_);
lean_dec(v___x_2137_);
v_eAssignment_2139_ = lean_ctor_get(v_mctx_2138_, 8);
lean_inc_ref(v_eAssignment_2139_);
lean_dec_ref(v_mctx_2138_);
v___x_2140_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_2139_, v_mvarId_2134_);
lean_dec_ref(v_eAssignment_2139_);
v___x_2141_ = lean_box(v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec(v_mvarId_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_2147_, size_t v_i_2148_, size_t v_stop_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_a_2162_; uint8_t v___x_2166_; 
v___x_2166_ = lean_usize_dec_eq(v_i_2148_, v_stop_2149_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v_mvarId_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_array_uget_borrowed(v_as_2147_, v_i_2148_);
v_mvarId_2168_ = lean_ctor_get(v___x_2167_, 1);
v___x_2169_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2168_, v___y_2157_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; uint8_t v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_unbox(v_a_2170_);
lean_dec(v_a_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
lean_inc(v___x_2167_);
v___x_2172_ = lean_array_push(v_b_2150_, v___x_2167_);
v_a_2162_ = v___x_2172_;
goto v___jp_2161_;
}
else
{
v_a_2162_ = v_b_2150_;
goto v___jp_2161_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_b_2150_);
v_a_2173_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2169_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2169_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_b_2150_);
return v___x_2181_;
}
v___jp_2161_:
{
size_t v___x_2163_; size_t v___x_2164_; 
v___x_2163_ = ((size_t)1ULL);
v___x_2164_ = lean_usize_add(v_i_2148_, v___x_2163_);
v_i_2148_ = v___x_2164_;
v_b_2150_ = v_a_2162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_2182_, lean_object* v_i_2183_, lean_object* v_stop_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
size_t v_i_boxed_2196_; size_t v_stop_boxed_2197_; lean_object* v_res_2198_; 
v_i_boxed_2196_ = lean_unbox_usize(v_i_2183_);
lean_dec(v_i_2183_);
v_stop_boxed_2197_ = lean_unbox_usize(v_stop_2184_);
lean_dec(v_stop_2184_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_2182_, v_i_boxed_2196_, v_stop_boxed_2197_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v_as_2182_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_2200_, size_t v_i_2201_, lean_object* v_bs_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = lean_usize_dec_lt(v_i_2201_, v_sz_2200_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_bs_2202_);
return v___x_2209_;
}
else
{
lean_object* v_v_2210_; lean_object* v_mvarId_2211_; lean_object* v___x_2212_; lean_object* v_bs_x27_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_v_2210_ = lean_array_uget_borrowed(v_bs_2202_, v_i_2201_);
v_mvarId_2211_ = lean_ctor_get(v_v_2210_, 1);
lean_inc_n(v_mvarId_2211_, 2);
v___x_2212_ = lean_unsigned_to_nat(0u);
v_bs_x27_2213_ = lean_array_uset(v_bs_2202_, v_i_2201_, v___x_2212_);
v___x_2214_ = lean_usize_to_nat(v_i_2201_);
v___x_2215_ = l_Lean_MVarId_getTag(v_mvarId_2211_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v___x_2217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_add(v___x_2214_, v___x_2218_);
lean_dec(v___x_2214_);
v___x_2220_ = l_Nat_reprFast(v___x_2219_);
v___x_2221_ = lean_string_append(v___x_2217_, v___x_2220_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = lean_box(0);
v___x_2223_ = l_Lean_Name_str___override(v___x_2222_, v___x_2221_);
v___x_2224_ = l_Lean_Name_eraseMacroScopes(v_a_2216_);
lean_dec(v_a_2216_);
v___x_2225_ = l_Lean_Name_append(v___x_2223_, v___x_2224_);
v___x_2226_ = l_Lean_MVarId_setTag___redArg(v_mvarId_2211_, v___x_2225_, v___y_2204_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_add(v_i_2201_, v___x_2228_);
v___x_2230_ = lean_array_uset(v_bs_x27_2213_, v_i_2201_, v_a_2227_);
v_i_2201_ = v___x_2229_;
v_bs_2202_ = v___x_2230_;
goto _start;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_bs_x27_2213_);
v_a_2232_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2226_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2226_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v___x_2214_);
lean_dec_ref(v_bs_x27_2213_);
lean_dec(v_mvarId_2211_);
v_a_2240_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2215_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2215_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_2248_, lean_object* v_i_2249_, lean_object* v_bs_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
size_t v_sz_boxed_2256_; size_t v_i_boxed_2257_; lean_object* v_res_2258_; 
v_sz_boxed_2256_ = lean_unbox_usize(v_sz_2248_);
lean_dec(v_sz_2248_);
v_i_boxed_2257_ = lean_unbox_usize(v_i_2249_);
lean_dec(v_i_2249_);
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_2256_, v_i_boxed_2257_, v_bs_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_2260_, size_t v_i_2261_, lean_object* v_bs_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v___x_2265_; 
v___x_2265_ = lean_usize_dec_lt(v_i_2261_, v_sz_2260_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; 
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v_bs_2262_);
return v___x_2266_;
}
else
{
lean_object* v_v_2267_; lean_object* v___x_2268_; lean_object* v_bs_x27_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_v_2267_ = lean_array_uget(v_bs_2262_, v_i_2261_);
v___x_2268_ = lean_unsigned_to_nat(0u);
v_bs_x27_2269_ = lean_array_uset(v_bs_2262_, v_i_2261_, v___x_2268_);
v___x_2270_ = lean_usize_to_nat(v_i_2261_);
v___x_2271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_add(v___x_2270_, v___x_2272_);
lean_dec(v___x_2270_);
v___x_2274_ = l_Nat_reprFast(v___x_2273_);
v___x_2275_ = lean_string_append(v___x_2271_, v___x_2274_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = lean_box(0);
v___x_2277_ = l_Lean_Name_str___override(v___x_2276_, v___x_2275_);
v___x_2278_ = l_Lean_MVarId_setTag___redArg(v_v_2267_, v___x_2277_, v___y_2263_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_add(v_i_2261_, v___x_2280_);
v___x_2282_ = lean_array_uset(v_bs_x27_2269_, v_i_2261_, v_a_2279_);
v_i_2261_ = v___x_2281_;
v_bs_2262_ = v___x_2282_;
goto _start;
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_bs_x27_2269_);
v_a_2284_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2278_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2278_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_2292_, lean_object* v_i_2293_, lean_object* v_bs_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
size_t v_sz_boxed_2297_; size_t v_i_boxed_2298_; lean_object* v_res_2299_; 
v_sz_boxed_2297_ = lean_unbox_usize(v_sz_2292_);
lean_dec(v_sz_2292_);
v_i_boxed_2298_ = lean_unbox_usize(v_i_2293_);
lean_dec(v_i_2293_);
v_res_2299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_2297_, v_i_boxed_2298_, v_bs_2294_, v___y_2295_);
lean_dec(v___y_2295_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_2300_, size_t v_i_2301_, size_t v_stop_2302_, lean_object* v_b_2303_){
_start:
{
lean_object* v___y_2305_; uint8_t v___x_2309_; 
v___x_2309_ = lean_usize_dec_eq(v_i_2301_, v_stop_2302_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; uint8_t v_retired_2311_; 
v___x_2310_ = lean_array_uget_borrowed(v_as_2300_, v_i_2301_);
v_retired_2311_ = lean_ctor_get_uint8(v___x_2310_, sizeof(void*)*4);
if (v_retired_2311_ == 0)
{
lean_object* v_frameStx_2312_; lean_object* v___x_2313_; 
v_frameStx_2312_ = lean_ctor_get(v___x_2310_, 2);
lean_inc(v_frameStx_2312_);
v___x_2313_ = lean_array_push(v_b_2303_, v_frameStx_2312_);
v___y_2305_ = v___x_2313_;
goto v___jp_2304_;
}
else
{
v___y_2305_ = v_b_2303_;
goto v___jp_2304_;
}
}
else
{
return v_b_2303_;
}
v___jp_2304_:
{
size_t v___x_2306_; size_t v___x_2307_; 
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_add(v_i_2301_, v___x_2306_);
v_i_2301_ = v___x_2307_;
v_b_2303_ = v___y_2305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_2314_, lean_object* v_i_2315_, lean_object* v_stop_2316_, lean_object* v_b_2317_){
_start:
{
size_t v_i_boxed_2318_; size_t v_stop_boxed_2319_; lean_object* v_res_2320_; 
v_i_boxed_2318_ = lean_unbox_usize(v_i_2315_);
lean_dec(v_i_2315_);
v_stop_boxed_2319_ = lean_unbox_usize(v_stop_2316_);
lean_dec(v_stop_2316_);
v_res_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2314_, v_i_boxed_2318_, v_stop_boxed_2319_, v_b_2317_);
lean_dec_ref(v_as_2314_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_2323_, lean_object* v_start_2324_, lean_object* v_stop_2325_){
_start:
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___closed__0));
v___x_2327_ = lean_nat_dec_lt(v_start_2324_, v_stop_2325_);
if (v___x_2327_ == 0)
{
return v___x_2326_;
}
else
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_array_get_size(v_as_2323_);
v___x_2329_ = lean_nat_dec_le(v_stop_2325_, v___x_2328_);
if (v___x_2329_ == 0)
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_nat_dec_lt(v_start_2324_, v___x_2328_);
if (v___x_2330_ == 0)
{
return v___x_2326_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_usize_of_nat(v_start_2324_);
v___x_2332_ = lean_usize_of_nat(v___x_2328_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2323_, v___x_2331_, v___x_2332_, v___x_2326_);
return v___x_2333_;
}
}
else
{
size_t v___x_2334_; size_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_usize_of_nat(v_start_2324_);
v___x_2335_ = lean_usize_of_nat(v_stop_2325_);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2323_, v___x_2334_, v___x_2335_, v___x_2326_);
return v___x_2336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_2337_, lean_object* v_start_2338_, lean_object* v_stop_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_2337_, v_start_2338_, v_stop_2339_);
lean_dec(v_stop_2339_);
lean_dec(v_start_2338_);
lean_dec_ref(v_as_2337_);
return v_res_2340_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_unsigned_to_nat(16u);
v___x_2343_ = lean_mk_array(v___x_2342_, v___x_2341_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2344_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v___x_2350_);
lean_ctor_set(v___x_2352_, 2, v___x_2350_);
lean_ctor_set(v___x_2352_, 3, v___x_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_2353_, lean_object* v_ctx_2354_, lean_object* v_scope_2355_, lean_object* v_stepLimit_x3f_2356_, lean_object* v_frameDB_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___x_2368_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v_a_2373_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___y_2383_; 
v___x_2368_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_2380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_2381_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_2356_) == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_box(1);
v___y_2383_ = v___x_2435_;
goto v___jp_2382_;
}
else
{
lean_object* v_val_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_val_2436_ = lean_ctor_get(v_stepLimit_x3f_2356_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_stepLimit_x3f_2356_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v_stepLimit_x3f_2356_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_val_2436_);
lean_dec(v_stepLimit_x3f_2356_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 0);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_val_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
v___y_2383_ = v___x_2441_;
goto v___jp_2382_;
}
}
}
v___jp_2369_:
{
lean_object* v_entries_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_entries_2374_ = lean_ctor_get(v___y_2370_, 1);
lean_inc_ref(v_entries_2374_);
lean_dec_ref(v___y_2370_);
v___x_2375_ = lean_array_get_size(v_entries_2374_);
v___x_2376_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_2374_, v___x_2368_, v___x_2375_);
lean_dec_ref(v_entries_2374_);
v___x_2377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2377_, 0, v___y_2371_);
lean_ctor_set(v___x_2377_, 1, v_a_2373_);
lean_ctor_set(v___x_2377_, 2, v___y_2372_);
lean_ctor_set(v___x_2377_, 3, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
v___jp_2382_:
{
lean_object* v_initState_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; 
v_initState_2384_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_initState_2384_, 0, v___x_2379_);
lean_ctor_set(v_initState_2384_, 1, v___x_2379_);
lean_ctor_set(v_initState_2384_, 2, v___x_2379_);
lean_ctor_set(v_initState_2384_, 3, v___x_2379_);
lean_ctor_set(v_initState_2384_, 4, v_frameDB_2357_);
lean_ctor_set(v_initState_2384_, 5, v___x_2380_);
lean_ctor_set(v_initState_2384_, 6, v___x_2380_);
lean_ctor_set(v_initState_2384_, 7, v___x_2381_);
lean_ctor_set(v_initState_2384_, 8, v___y_2383_);
lean_ctor_set(v_initState_2384_, 9, v___x_2379_);
lean_ctor_set(v_initState_2384_, 10, v___x_2379_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2385_, 0, v_initState_2384_);
lean_closure_set(v___f_2385_, 1, v_scope_2355_);
lean_closure_set(v___f_2385_, 2, v_goal_2353_);
lean_closure_set(v___f_2385_, 3, v_ctx_2354_);
v___x_2386_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_2385_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v_snd_2388_; lean_object* v_frameDB_2389_; lean_object* v_invariants_2390_; lean_object* v_vcs_2391_; lean_object* v_inlineHandledInvariants_2392_; size_t v_sz_2393_; size_t v___x_2394_; lean_object* v___x_2395_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v_snd_2388_ = lean_ctor_get(v_a_2387_, 1);
lean_inc(v_snd_2388_);
lean_dec(v_a_2387_);
v_frameDB_2389_ = lean_ctor_get(v_snd_2388_, 4);
lean_inc_ref(v_frameDB_2389_);
v_invariants_2390_ = lean_ctor_get(v_snd_2388_, 5);
lean_inc_ref_n(v_invariants_2390_, 2);
v_vcs_2391_ = lean_ctor_get(v_snd_2388_, 6);
lean_inc_ref(v_vcs_2391_);
v_inlineHandledInvariants_2392_ = lean_ctor_get(v_snd_2388_, 9);
lean_inc_ref(v_inlineHandledInvariants_2392_);
lean_dec(v_snd_2388_);
v_sz_2393_ = lean_array_size(v_invariants_2390_);
v___x_2394_ = ((size_t)0ULL);
v___x_2395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_2393_, v___x_2394_, v_invariants_2390_, v_a_2364_);
if (lean_obj_tag(v___x_2395_) == 0)
{
size_t v_sz_2396_; lean_object* v___x_2397_; 
lean_dec_ref_known(v___x_2395_, 1);
v_sz_2396_ = lean_array_size(v_vcs_2391_);
lean_inc_ref(v_vcs_2391_);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2396_, v___x_2394_, v_vcs_2391_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
lean_dec_ref_known(v___x_2397_, 1);
v___x_2398_ = lean_array_get_size(v_vcs_2391_);
v___x_2399_ = lean_nat_dec_lt(v___x_2368_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec_ref(v_vcs_2391_);
v___y_2370_ = v_frameDB_2389_;
v___y_2371_ = v_invariants_2390_;
v___y_2372_ = v_inlineHandledInvariants_2392_;
v_a_2373_ = v___x_2380_;
goto v___jp_2369_;
}
else
{
size_t v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_usize_of_nat(v___x_2398_);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_2391_, v___x_2394_, v___x_2400_, v___x_2380_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec_ref(v_vcs_2391_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v___y_2370_ = v_frameDB_2389_;
v___y_2371_ = v_invariants_2390_;
v___y_2372_ = v_inlineHandledInvariants_2392_;
v_a_2373_ = v_a_2402_;
goto v___jp_2369_;
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec_ref(v_inlineHandledInvariants_2392_);
lean_dec_ref(v_invariants_2390_);
lean_dec_ref(v_frameDB_2389_);
v_a_2403_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2401_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2401_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v_inlineHandledInvariants_2392_);
lean_dec_ref(v_vcs_2391_);
lean_dec_ref(v_invariants_2390_);
lean_dec_ref(v_frameDB_2389_);
v_a_2411_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2397_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2397_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref(v_inlineHandledInvariants_2392_);
lean_dec_ref(v_vcs_2391_);
lean_dec_ref(v_invariants_2390_);
lean_dec_ref(v_frameDB_2389_);
v_a_2419_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2395_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2395_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_a_2427_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2386_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2386_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_2444_, lean_object* v_ctx_2445_, lean_object* v_scope_2446_, lean_object* v_stepLimit_x3f_2447_, lean_object* v_frameDB_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_2444_, v_ctx_2445_, v_scope_2446_, v_stepLimit_x3f_2447_, v_frameDB_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2460_, v___y_2467_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec(v_mvarId_2472_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_2484_, size_t v_sz_2485_, size_t v_i_2486_, lean_object* v_bs_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_2485_, v_i_2486_, v_bs_2487_, v___y_2494_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_2499_, lean_object* v_sz_2500_, lean_object* v_i_2501_, lean_object* v_bs_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
size_t v_sz_boxed_2513_; size_t v_i_boxed_2514_; lean_object* v_res_2515_; 
v_sz_boxed_2513_ = lean_unbox_usize(v_sz_2500_);
lean_dec(v_sz_2500_);
v_i_boxed_2514_ = lean_unbox_usize(v_i_2501_);
lean_dec(v_i_2501_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_2499_, v_sz_boxed_2513_, v_i_boxed_2514_, v_bs_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v_as_2499_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_2516_, size_t v_sz_2517_, size_t v_i_2518_, lean_object* v_bs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2517_, v_i_2518_, v_bs_2519_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_2531_, lean_object* v_sz_2532_, lean_object* v_i_2533_, lean_object* v_bs_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
size_t v_sz_boxed_2545_; size_t v_i_boxed_2546_; lean_object* v_res_2547_; 
v_sz_boxed_2545_ = lean_unbox_usize(v_sz_2532_);
lean_dec(v_sz_2532_);
v_i_boxed_2546_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_res_2547_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_2531_, v_sz_boxed_2545_, v_i_boxed_2546_, v_bs_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v_as_2531_);
return v_res_2547_;
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
