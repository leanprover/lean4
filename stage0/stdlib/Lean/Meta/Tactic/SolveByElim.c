// Lean compiler output
// Module: Lean.Meta.Tactic.SolveByElim
// Imports: public import Init.Data.Sum public import Lean.LabelAttribute public import Lean.Meta.Tactic.Backtrack public import Lean.Meta.Tactic.Constructor public import Lean.Meta.Tactic.Repeat public import Lean.Meta.Tactic.Symm public import Lean.Elab.Term
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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_ofList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_head___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveByElim"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 179, 43, 63, 49, 24, 32, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SolveByElim"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 124, 130, 51, 187, 220, 69, 235)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(217, 20, 184, 114, 46, 152, 175, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 70, 43, 38, 54, 221, 118, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 139, 182, 61, 70, 53, 35, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 96, 167, 3, 193, 174, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 99, 190, 156, 65, 10, 108, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 198, 193, 11, 27, 150, 253, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 168, 148, 157, 214, 227, 227, 54)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 34, 196, 227, 75, 22, 166, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 42, 156, 241, 147, 248, 49, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 159, 244, 240, 243, 215, 3, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__23_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1979843508) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 117, 78, 143, 26, 177, 227, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__24_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__25_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 86, 236, 87, 154, 213, 60, 227)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__26_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__27_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 78, 242, 178, 10, 32, 62, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__28_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(167, 116, 242, 130, 86, 112, 31, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "trying to apply: "};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object*);
static const lean_ctor_object l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object*);
static const lean_ctor_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value;
static const lean_array_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3 = (const lean_object*)&l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`repeat1'` made no progress"};
static const lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 32, .m_data = "⏮️ starting over using `exfalso`"};
static const lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_SolveByElim_solveByElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_solveByElim___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_solveByElim___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "It doesn't make sense to remove local hypotheses when using `only` without `*`."};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5_value),LEAN_SCALAR_PTR_LITERAL(16, 215, 57, 166, 49, 41, 228, 20)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21_value;
static const lean_array_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22_value;
static const lean_string_object l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "It doesn't make sense to use `*` without `only`."};
static const lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23 = (const lean_object*)&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_74_ = 0;
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__29_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_76_ = l_Lean_registerTraceClass(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
return v_res_78_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(32u);
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(32u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0);
v___x_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
lean_ctor_set(v___x_87_, 3, v___x_83_);
lean_ctor_set_usize(v___x_87_, 4, v___x_82_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_traceState_91_; lean_object* v_traces_92_; lean_object* v___x_93_; lean_object* v_traceState_94_; lean_object* v_env_95_; lean_object* v_nextMacroScope_96_; lean_object* v_ngen_97_; lean_object* v_auxDeclNGen_98_; lean_object* v_cache_99_; lean_object* v_messages_100_; lean_object* v_infoState_101_; lean_object* v_snapshotTasks_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_121_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_traceState_91_ = lean_ctor_get(v___x_90_, 4);
lean_inc_ref(v_traceState_91_);
lean_dec(v___x_90_);
v_traces_92_ = lean_ctor_get(v_traceState_91_, 0);
lean_inc_ref(v_traces_92_);
lean_dec_ref(v_traceState_91_);
v___x_93_ = lean_st_ref_take(v___y_88_);
v_traceState_94_ = lean_ctor_get(v___x_93_, 4);
v_env_95_ = lean_ctor_get(v___x_93_, 0);
v_nextMacroScope_96_ = lean_ctor_get(v___x_93_, 1);
v_ngen_97_ = lean_ctor_get(v___x_93_, 2);
v_auxDeclNGen_98_ = lean_ctor_get(v___x_93_, 3);
v_cache_99_ = lean_ctor_get(v___x_93_, 5);
v_messages_100_ = lean_ctor_get(v___x_93_, 6);
v_infoState_101_ = lean_ctor_get(v___x_93_, 7);
v_snapshotTasks_102_ = lean_ctor_get(v___x_93_, 8);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_121_ == 0)
{
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_snapshotTasks_102_);
lean_inc(v_infoState_101_);
lean_inc(v_messages_100_);
lean_inc(v_cache_99_);
lean_inc(v_traceState_94_);
lean_inc(v_auxDeclNGen_98_);
lean_inc(v_ngen_97_);
lean_inc(v_nextMacroScope_96_);
lean_inc(v_env_95_);
lean_dec(v___x_93_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint64_t v_tid_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_119_; 
v_tid_106_ = lean_ctor_get_uint64(v_traceState_94_, sizeof(void*)*1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_traceState_94_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v_traceState_94_, 0);
lean_dec(v_unused_120_);
v___x_108_ = v_traceState_94_;
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_traceState_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_119_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_110_);
lean_ctor_set_uint64(v_reuseFailAlloc_118_, sizeof(void*)*1, v_tid_106_);
v___x_112_ = v_reuseFailAlloc_118_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_114_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 4, v___x_112_);
v___x_114_ = v___x_104_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_env_95_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_nextMacroScope_96_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_ngen_97_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_auxDeclNGen_98_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_117_, 5, v_cache_99_);
lean_ctor_set(v_reuseFailAlloc_117_, 6, v_messages_100_);
lean_ctor_set(v_reuseFailAlloc_117_, 7, v_infoState_101_);
lean_ctor_set(v_reuseFailAlloc_117_, 8, v_snapshotTasks_102_);
v___x_114_ = v_reuseFailAlloc_117_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_st_ref_set(v___y_88_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_traces_92_);
return v___x_116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_122_);
lean_dec(v___y_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
lean_object* v_name_139_; lean_object* v_defValue_140_; lean_object* v_map_141_; lean_object* v___x_142_; 
v_name_139_ = lean_ctor_get(v_opt_138_, 0);
v_defValue_140_ = lean_ctor_get(v_opt_138_, 1);
v_map_141_ = lean_ctor_get(v_opts_137_, 0);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_141_, v_name_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = lean_unbox(v_defValue_140_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; 
v_val_144_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_142_, 1);
if (lean_obj_tag(v_val_144_) == 1)
{
uint8_t v_v_145_; 
v_v_145_ = lean_ctor_get_uint8(v_val_144_, 0);
lean_dec_ref_known(v_val_144_, 0);
return v_v_145_;
}
else
{
uint8_t v___x_146_; 
lean_dec(v_val_144_);
v___x_146_ = lean_unbox(v_defValue_140_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_147_, v_opt_148_);
lean_dec_ref(v_opt_148_);
lean_dec_ref(v_opts_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_saveState___redArg(v___y_153_, v___y_155_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
v___x_159_ = lean_apply_5(v_x_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, lean_box(0));
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_a_158_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___x_159_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_198_; 
v_a_169_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_198_ == 0)
{
v___x_171_ = v___x_159_;
v_isShared_172_ = v_isSharedCheck_198_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_159_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_198_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___y_174_; uint8_t v___x_196_; 
v___x_196_ = l_Lean_Exception_isInterrupt(v_a_169_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_inc(v_a_169_);
v___x_197_ = l_Lean_Exception_isRuntime(v_a_169_);
v___y_174_ = v___x_197_;
goto v___jp_173_;
}
else
{
v___y_174_ = v___x_196_;
goto v___jp_173_;
}
v___jp_173_:
{
if (v___y_174_ == 0)
{
lean_object* v___x_175_; 
lean_del_object(v___x_171_);
lean_dec(v_a_169_);
v___x_175_ = l_Lean_Meta_SavedState_restore___redArg(v_a_158_, v___y_153_, v___y_155_);
lean_dec(v_a_158_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_175_, 0);
lean_dec(v_unused_184_);
v___x_177_ = v___x_175_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_dec(v___x_175_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_175_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_175_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
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
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_a_158_);
if (v_isShared_172_ == 0)
{
v___x_194_ = v___x_171_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_169_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v_x_151_);
v_a_199_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_157_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_157_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
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
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_222_, lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_222_, v_x_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_233_, lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_241_ = l_Lean_MessageData_ofExpr(v_e_233_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_244_, lean_object* v_x_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v_x_245_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_252_, uint8_t v___x_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_x_255_);
return v___x_261_;
}
else
{
lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_287_; 
v_head_262_ = lean_ctor_get(v_x_254_, 0);
v_tail_263_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_287_ == 0)
{
v___x_265_ = v_x_254_;
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_tail_263_);
lean_inc(v_head_262_);
lean_dec(v_x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v_a_268_; lean_object* v___x_274_; 
lean_inc(v_head_262_);
v___x_274_ = l_Lean_MVarId_inferInstance(v_head_262_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_dec_ref_known(v___x_274_, 1);
v_a_268_ = v___x_252_;
goto v___jp_267_;
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_286_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_286_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_286_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v___y_280_; uint8_t v___x_284_; 
v___x_284_ = l_Lean_Exception_isInterrupt(v_a_275_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc(v_a_275_);
v___x_285_ = l_Lean_Exception_isRuntime(v_a_275_);
v___y_280_ = v___x_285_;
goto v___jp_279_;
}
else
{
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
lean_del_object(v___x_277_);
lean_dec(v_a_275_);
v_a_268_ = v___x_253_;
goto v___jp_267_;
}
else
{
lean_object* v___x_282_; 
lean_del_object(v___x_265_);
lean_dec(v_tail_263_);
lean_dec(v_head_262_);
lean_dec(v_x_255_);
if (v_isShared_278_ == 0)
{
v___x_282_ = v___x_277_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_275_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
v___jp_267_:
{
if (v_a_268_ == 0)
{
lean_del_object(v___x_265_);
lean_dec(v_head_262_);
v_x_254_ = v_tail_263_;
goto _start;
}
else
{
lean_object* v___x_271_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_x_255_);
v___x_271_ = v___x_265_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_head_262_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_x_255_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v_x_254_ = v_tail_263_;
v_x_255_ = v___x_271_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___x_12977__boxed_297_; uint8_t v___x_12978__boxed_298_; lean_object* v_res_299_; 
v___x_12977__boxed_297_ = lean_unbox(v___x_288_);
v___x_12978__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_12977__boxed_297_, v___x_12978__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_env_307_; lean_object* v___x_308_; lean_object* v_mctx_309_; lean_object* v_lctx_310_; lean_object* v_options_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_env_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_env_307_);
lean_dec(v___x_306_);
v___x_308_ = lean_st_ref_get(v___y_302_);
v_mctx_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_309_);
lean_dec(v___x_308_);
v_lctx_310_ = lean_ctor_get(v___y_301_, 2);
v_options_311_ = lean_ctor_get(v___y_303_, 2);
lean_inc_ref(v_options_311_);
lean_inc_ref(v_lctx_310_);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_env_307_);
lean_ctor_set(v___x_312_, 1, v_mctx_309_);
lean_ctor_set(v___x_312_, 2, v_lctx_310_);
lean_ctor_set(v___x_312_, 3, v_options_311_);
v___x_313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_msgData_300_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5___boxed(lean_object* v_msgData_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msgData_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(size_t v_sz_322_, size_t v_i_323_, lean_object* v_bs_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_325_ == 0)
{
return v_bs_324_;
}
else
{
lean_object* v_v_326_; lean_object* v_msg_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v_v_326_ = lean_array_uget_borrowed(v_bs_324_, v_i_323_);
v_msg_327_ = lean_ctor_get(v_v_326_, 1);
lean_inc_ref(v_msg_327_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_324_, v_i_323_, v___x_328_);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_323_, v___x_330_);
v___x_332_ = lean_array_uset(v_bs_x27_329_, v_i_323_, v_msg_327_);
v_i_323_ = v___x_331_;
v_bs_324_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_bs_336_){
_start:
{
size_t v_sz_boxed_337_; size_t v_i_boxed_338_; lean_object* v_res_339_; 
v_sz_boxed_337_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_boxed_337_, v_i_boxed_338_, v_bs_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_oldTraces_340_, lean_object* v_data_341_, lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_fileName_349_; lean_object* v_fileMap_350_; lean_object* v_options_351_; lean_object* v_currRecDepth_352_; lean_object* v_maxRecDepth_353_; lean_object* v_ref_354_; lean_object* v_currNamespace_355_; lean_object* v_openDecls_356_; lean_object* v_initHeartbeats_357_; lean_object* v_maxHeartbeats_358_; lean_object* v_quotContext_359_; lean_object* v_currMacroScope_360_; uint8_t v_diag_361_; lean_object* v_cancelTk_x3f_362_; uint8_t v_suppressElabErrors_363_; lean_object* v_inheritedTraceOptions_364_; lean_object* v___x_365_; lean_object* v_traceState_366_; lean_object* v_traces_367_; lean_object* v_ref_368_; lean_object* v___x_369_; lean_object* v___x_370_; size_t v_sz_371_; size_t v___x_372_; lean_object* v___x_373_; lean_object* v_msg_374_; lean_object* v___x_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_413_; 
v_fileName_349_ = lean_ctor_get(v___y_346_, 0);
v_fileMap_350_ = lean_ctor_get(v___y_346_, 1);
v_options_351_ = lean_ctor_get(v___y_346_, 2);
v_currRecDepth_352_ = lean_ctor_get(v___y_346_, 3);
v_maxRecDepth_353_ = lean_ctor_get(v___y_346_, 4);
v_ref_354_ = lean_ctor_get(v___y_346_, 5);
v_currNamespace_355_ = lean_ctor_get(v___y_346_, 6);
v_openDecls_356_ = lean_ctor_get(v___y_346_, 7);
v_initHeartbeats_357_ = lean_ctor_get(v___y_346_, 8);
v_maxHeartbeats_358_ = lean_ctor_get(v___y_346_, 9);
v_quotContext_359_ = lean_ctor_get(v___y_346_, 10);
v_currMacroScope_360_ = lean_ctor_get(v___y_346_, 11);
v_diag_361_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*14);
v_cancelTk_x3f_362_ = lean_ctor_get(v___y_346_, 12);
v_suppressElabErrors_363_ = lean_ctor_get_uint8(v___y_346_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_364_ = lean_ctor_get(v___y_346_, 13);
v___x_365_ = lean_st_ref_get(v___y_347_);
v_traceState_366_ = lean_ctor_get(v___x_365_, 4);
lean_inc_ref(v_traceState_366_);
lean_dec(v___x_365_);
v_traces_367_ = lean_ctor_get(v_traceState_366_, 0);
lean_inc_ref(v_traces_367_);
lean_dec_ref(v_traceState_366_);
v_ref_368_ = l_Lean_replaceRef(v_ref_342_, v_ref_354_);
lean_inc_ref(v_inheritedTraceOptions_364_);
lean_inc(v_cancelTk_x3f_362_);
lean_inc(v_currMacroScope_360_);
lean_inc(v_quotContext_359_);
lean_inc(v_maxHeartbeats_358_);
lean_inc(v_initHeartbeats_357_);
lean_inc(v_openDecls_356_);
lean_inc(v_currNamespace_355_);
lean_inc(v_maxRecDepth_353_);
lean_inc(v_currRecDepth_352_);
lean_inc_ref(v_options_351_);
lean_inc_ref(v_fileMap_350_);
lean_inc_ref(v_fileName_349_);
v___x_369_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_369_, 0, v_fileName_349_);
lean_ctor_set(v___x_369_, 1, v_fileMap_350_);
lean_ctor_set(v___x_369_, 2, v_options_351_);
lean_ctor_set(v___x_369_, 3, v_currRecDepth_352_);
lean_ctor_set(v___x_369_, 4, v_maxRecDepth_353_);
lean_ctor_set(v___x_369_, 5, v_ref_368_);
lean_ctor_set(v___x_369_, 6, v_currNamespace_355_);
lean_ctor_set(v___x_369_, 7, v_openDecls_356_);
lean_ctor_set(v___x_369_, 8, v_initHeartbeats_357_);
lean_ctor_set(v___x_369_, 9, v_maxHeartbeats_358_);
lean_ctor_set(v___x_369_, 10, v_quotContext_359_);
lean_ctor_set(v___x_369_, 11, v_currMacroScope_360_);
lean_ctor_set(v___x_369_, 12, v_cancelTk_x3f_362_);
lean_ctor_set(v___x_369_, 13, v_inheritedTraceOptions_364_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*14, v_diag_361_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*14 + 1, v_suppressElabErrors_363_);
v___x_370_ = l_Lean_PersistentArray_toArray___redArg(v_traces_367_);
lean_dec_ref(v_traces_367_);
v_sz_371_ = lean_array_size(v___x_370_);
v___x_372_ = ((size_t)0ULL);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__4(v_sz_371_, v___x_372_, v___x_370_);
v_msg_374_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_374_, 0, v_data_341_);
lean_ctor_set(v_msg_374_, 1, v_msg_343_);
lean_ctor_set(v_msg_374_, 2, v___x_373_);
v___x_375_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_374_, v___y_344_, v___y_345_, v___x_369_, v___y_347_);
lean_dec_ref_known(v___x_369_, 14);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_413_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_413_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_413_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v_traceState_381_; lean_object* v_env_382_; lean_object* v_nextMacroScope_383_; lean_object* v_ngen_384_; lean_object* v_auxDeclNGen_385_; lean_object* v_cache_386_; lean_object* v_messages_387_; lean_object* v_infoState_388_; lean_object* v_snapshotTasks_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_412_; 
v___x_380_ = lean_st_ref_take(v___y_347_);
v_traceState_381_ = lean_ctor_get(v___x_380_, 4);
v_env_382_ = lean_ctor_get(v___x_380_, 0);
v_nextMacroScope_383_ = lean_ctor_get(v___x_380_, 1);
v_ngen_384_ = lean_ctor_get(v___x_380_, 2);
v_auxDeclNGen_385_ = lean_ctor_get(v___x_380_, 3);
v_cache_386_ = lean_ctor_get(v___x_380_, 5);
v_messages_387_ = lean_ctor_get(v___x_380_, 6);
v_infoState_388_ = lean_ctor_get(v___x_380_, 7);
v_snapshotTasks_389_ = lean_ctor_get(v___x_380_, 8);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_412_ == 0)
{
v___x_391_ = v___x_380_;
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snapshotTasks_389_);
lean_inc(v_infoState_388_);
lean_inc(v_messages_387_);
lean_inc(v_cache_386_);
lean_inc(v_traceState_381_);
lean_inc(v_auxDeclNGen_385_);
lean_inc(v_ngen_384_);
lean_inc(v_nextMacroScope_383_);
lean_inc(v_env_382_);
lean_dec(v___x_380_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint64_t v_tid_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_410_; 
v_tid_393_ = lean_ctor_get_uint64(v_traceState_381_, sizeof(void*)*1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_traceState_381_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_traceState_381_, 0);
lean_dec(v_unused_411_);
v___x_395_ = v_traceState_381_;
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_traceState_381_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_410_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_ref_342_);
lean_ctor_set(v___x_397_, 1, v_a_376_);
v___x_398_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_340_, v___x_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_398_);
lean_ctor_set_uint64(v_reuseFailAlloc_409_, sizeof(void*)*1, v_tid_393_);
v___x_400_ = v_reuseFailAlloc_409_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_402_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_400_);
v___x_402_ = v___x_391_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_env_382_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_nextMacroScope_383_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_ngen_384_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_auxDeclNGen_385_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_408_, 5, v_cache_386_);
lean_ctor_set(v_reuseFailAlloc_408_, 6, v_messages_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 7, v_infoState_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 8, v_snapshotTasks_389_);
v___x_402_ = v_reuseFailAlloc_408_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_st_ref_set(v___y_347_, v___x_402_);
v___x_404_ = lean_box(0);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_404_);
v___x_406_ = v___x_378_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_oldTraces_414_, lean_object* v_data_415_, lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_414_, v_data_415_, v_ref_416_, v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_e_424_){
_start:
{
if (lean_obj_tag(v_e_424_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 2;
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_e_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_e_427_);
lean_dec_ref(v_e_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_430_, lean_object* v_opt_431_){
_start:
{
lean_object* v_name_432_; lean_object* v_defValue_433_; lean_object* v_map_434_; lean_object* v___x_435_; 
v_name_432_ = lean_ctor_get(v_opt_431_, 0);
v_defValue_433_ = lean_ctor_get(v_opt_431_, 1);
v_map_434_ = lean_ctor_get(v_opts_430_, 0);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_434_, v_name_432_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_inc(v_defValue_433_);
return v_defValue_433_;
}
else
{
lean_object* v_val_436_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
if (lean_obj_tag(v_val_436_) == 3)
{
lean_object* v_v_437_; 
v_v_437_ = lean_ctor_get(v_val_436_, 0);
lean_inc(v_v_437_);
lean_dec_ref_known(v_val_436_, 1);
return v_v_437_;
}
else
{
lean_dec(v_val_436_);
lean_inc(v_defValue_433_);
return v_defValue_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_438_, lean_object* v_opt_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_438_, v_opt_439_);
lean_dec_ref(v_opt_439_);
lean_dec_ref(v_opts_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v_x_441_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v_x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v_x_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v_x_441_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v_x_441_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 0);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg___boxed(lean_object* v_x_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_459_);
return v_res_461_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0(void){
_start:
{
lean_object* v___x_462_; double v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_float_of_nat(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3(void){
_start:
{
lean_object* v___x_467_; double v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1000u);
v___x_468_ = lean_float_of_nat(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_469_, uint8_t v_collapsed_470_, lean_object* v_tag_471_, lean_object* v_opts_472_, uint8_t v_clsEnabled_473_, lean_object* v_oldTraces_474_, lean_object* v_msg_475_, lean_object* v_resStartStop_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v_data_487_; lean_object* v_fst_498_; lean_object* v_snd_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___y_503_; lean_object* v_a_504_; uint8_t v___y_519_; double v___y_550_; 
v_fst_482_ = lean_ctor_get(v_resStartStop_476_, 0);
lean_inc(v_fst_482_);
v_snd_483_ = lean_ctor_get(v_resStartStop_476_, 1);
lean_inc(v_snd_483_);
lean_dec_ref(v_resStartStop_476_);
v_fst_498_ = lean_ctor_get(v_snd_483_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v_snd_483_, 1);
lean_inc(v_snd_499_);
lean_dec(v_snd_483_);
v___x_500_ = l_Lean_trace_profiler;
v___x_501_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_472_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_519_ = v___x_501_;
goto v___jp_518_;
}
else
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = l_Lean_trace_profiler_useHeartbeats;
v___x_556_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_472_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; double v___x_559_; double v___x_560_; double v___x_561_; 
v___x_557_ = l_Lean_trace_profiler_threshold;
v___x_558_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_472_, v___x_557_);
v___x_559_ = lean_float_of_nat(v___x_558_);
v___x_560_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3);
v___x_561_ = lean_float_div(v___x_559_, v___x_560_);
v___y_550_ = v___x_561_;
goto v___jp_549_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; double v___x_564_; 
v___x_562_ = l_Lean_trace_profiler_threshold;
v___x_563_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_472_, v___x_562_);
v___x_564_ = lean_float_of_nat(v___x_563_);
v___y_550_ = v___x_564_;
goto v___jp_549_;
}
}
v___jp_484_:
{
lean_object* v___x_488_; 
lean_inc(v___y_486_);
v___x_488_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_oldTraces_474_, v_data_487_, v___y_486_, v___y_485_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; 
lean_dec_ref_known(v___x_488_, 1);
v___x_489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_482_);
return v___x_489_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_fst_482_);
v_a_490_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_488_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_488_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
v___jp_502_:
{
uint8_t v_result_505_; lean_object* v___x_506_; lean_object* v___x_507_; double v___x_508_; lean_object* v_data_509_; 
v_result_505_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_fst_482_);
v___x_506_ = lean_box(v_result_505_);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
v___x_508_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0);
lean_inc_ref(v_tag_471_);
lean_inc_ref(v___x_507_);
lean_inc(v_cls_469_);
v_data_509_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_509_, 0, v_cls_469_);
lean_ctor_set(v_data_509_, 1, v___x_507_);
lean_ctor_set(v_data_509_, 2, v_tag_471_);
lean_ctor_set_float(v_data_509_, sizeof(void*)*3, v___x_508_);
lean_ctor_set_float(v_data_509_, sizeof(void*)*3 + 8, v___x_508_);
lean_ctor_set_uint8(v_data_509_, sizeof(void*)*3 + 16, v_collapsed_470_);
if (v___x_501_ == 0)
{
lean_dec_ref_known(v___x_507_, 1);
lean_dec(v_snd_499_);
lean_dec(v_fst_498_);
lean_dec_ref(v_tag_471_);
lean_dec(v_cls_469_);
v___y_485_ = v_a_504_;
v___y_486_ = v___y_503_;
v_data_487_ = v_data_509_;
goto v___jp_484_;
}
else
{
lean_object* v_data_510_; double v___x_511_; double v___x_512_; 
lean_dec_ref_known(v_data_509_, 3);
v_data_510_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_510_, 0, v_cls_469_);
lean_ctor_set(v_data_510_, 1, v___x_507_);
lean_ctor_set(v_data_510_, 2, v_tag_471_);
v___x_511_ = lean_unbox_float(v_fst_498_);
lean_dec(v_fst_498_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3, v___x_511_);
v___x_512_ = lean_unbox_float(v_snd_499_);
lean_dec(v_snd_499_);
lean_ctor_set_float(v_data_510_, sizeof(void*)*3 + 8, v___x_512_);
lean_ctor_set_uint8(v_data_510_, sizeof(void*)*3 + 16, v_collapsed_470_);
v___y_485_ = v_a_504_;
v___y_486_ = v___y_503_;
v_data_487_ = v_data_510_;
goto v___jp_484_;
}
}
v___jp_513_:
{
lean_object* v_ref_514_; lean_object* v___x_515_; 
v_ref_514_ = lean_ctor_get(v___y_479_, 5);
lean_inc(v___y_480_);
lean_inc_ref(v___y_479_);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
lean_inc(v_fst_482_);
v___x_515_ = lean_apply_6(v_msg_475_, v_fst_482_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, lean_box(0));
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___y_503_ = v_ref_514_;
v_a_504_ = v_a_516_;
goto v___jp_502_;
}
else
{
lean_object* v___x_517_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
v___y_503_ = v_ref_514_;
v_a_504_ = v___x_517_;
goto v___jp_502_;
}
}
v___jp_518_:
{
if (v_clsEnabled_473_ == 0)
{
if (v___y_519_ == 0)
{
lean_object* v___x_520_; lean_object* v_traceState_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_cache_526_; lean_object* v_messages_527_; lean_object* v_infoState_528_; lean_object* v_snapshotTasks_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_snd_499_);
lean_dec(v_fst_498_);
lean_dec_ref(v_msg_475_);
lean_dec_ref(v_tag_471_);
lean_dec(v_cls_469_);
v___x_520_ = lean_st_ref_take(v___y_480_);
v_traceState_521_ = lean_ctor_get(v___x_520_, 4);
v_env_522_ = lean_ctor_get(v___x_520_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_520_, 1);
v_ngen_524_ = lean_ctor_get(v___x_520_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_520_, 3);
v_cache_526_ = lean_ctor_get(v___x_520_, 5);
v_messages_527_ = lean_ctor_get(v___x_520_, 6);
v_infoState_528_ = lean_ctor_get(v___x_520_, 7);
v_snapshotTasks_529_ = lean_ctor_get(v___x_520_, 8);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_548_ == 0)
{
v___x_531_ = v___x_520_;
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snapshotTasks_529_);
lean_inc(v_infoState_528_);
lean_inc(v_messages_527_);
lean_inc(v_cache_526_);
lean_inc(v_traceState_521_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_520_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
uint64_t v_tid_533_; lean_object* v_traces_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_547_; 
v_tid_533_ = lean_ctor_get_uint64(v_traceState_521_, sizeof(void*)*1);
v_traces_534_ = lean_ctor_get(v_traceState_521_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_traceState_521_);
if (v_isSharedCheck_547_ == 0)
{
v___x_536_ = v_traceState_521_;
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_traces_534_);
lean_dec(v_traceState_521_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_547_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_474_, v_traces_534_);
lean_dec_ref(v_traces_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_538_);
lean_ctor_set_uint64(v_reuseFailAlloc_546_, sizeof(void*)*1, v_tid_533_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v___x_540_);
v___x_542_ = v___x_531_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_env_522_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_545_, 5, v_cache_526_);
lean_ctor_set(v_reuseFailAlloc_545_, 6, v_messages_527_);
lean_ctor_set(v_reuseFailAlloc_545_, 7, v_infoState_528_);
lean_ctor_set(v_reuseFailAlloc_545_, 8, v_snapshotTasks_529_);
v___x_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_st_ref_set(v___y_480_, v___x_542_);
v___x_544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_fst_482_);
return v___x_544_;
}
}
}
}
}
else
{
goto v___jp_513_;
}
}
else
{
goto v___jp_513_;
}
}
v___jp_549_:
{
double v___x_551_; double v___x_552_; double v___x_553_; uint8_t v___x_554_; 
v___x_551_ = lean_unbox_float(v_snd_499_);
v___x_552_ = lean_unbox_float(v_fst_498_);
v___x_553_ = lean_float_sub(v___x_551_, v___x_552_);
v___x_554_ = lean_float_decLt(v___y_550_, v___x_553_);
v___y_519_ = v___x_554_;
goto v___jp_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_565_, lean_object* v_collapsed_566_, lean_object* v_tag_567_, lean_object* v_opts_568_, lean_object* v_clsEnabled_569_, lean_object* v_oldTraces_570_, lean_object* v_msg_571_, lean_object* v_resStartStop_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v_collapsed_boxed_578_; uint8_t v_clsEnabled_boxed_579_; lean_object* v_res_580_; 
v_collapsed_boxed_578_ = lean_unbox(v_collapsed_566_);
v_clsEnabled_boxed_579_ = lean_unbox(v_clsEnabled_569_);
v_res_580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_565_, v_collapsed_boxed_578_, v_tag_567_, v_opts_568_, v_clsEnabled_boxed_579_, v_oldTraces_570_, v_msg_571_, v_resStartStop_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_opts_568_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_x_583_);
return v___x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_head_590_ = lean_ctor_get(v_x_582_, 0);
v_tail_591_ = lean_ctor_get(v_x_582_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v_x_582_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_head_590_);
lean_dec(v_x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
lean_inc(v_head_590_);
v___x_595_ = l_Lean_MVarId_inferInstance(v_head_590_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_dec_ref_known(v___x_595_, 1);
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
v_x_582_ = v_tail_591_;
goto _start;
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_613_; 
v_a_597_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_613_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_613_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_613_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v___y_602_; uint8_t v___x_611_; 
v___x_611_ = l_Lean_Exception_isInterrupt(v_a_597_);
if (v___x_611_ == 0)
{
uint8_t v___x_612_; 
lean_inc(v_a_597_);
v___x_612_ = l_Lean_Exception_isRuntime(v_a_597_);
v___y_602_ = v___x_612_;
goto v___jp_601_;
}
else
{
v___y_602_ = v___x_611_;
goto v___jp_601_;
}
v___jp_601_:
{
if (v___y_602_ == 0)
{
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
if (v___x_581_ == 0)
{
lean_del_object(v___x_593_);
lean_dec(v_head_590_);
v_x_582_ = v_tail_591_;
goto _start;
}
else
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v_x_583_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_head_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_x_583_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_x_582_ = v_tail_591_;
v_x_583_ = v___x_605_;
goto _start;
}
}
}
else
{
lean_object* v___x_609_; 
lean_del_object(v___x_593_);
lean_dec(v_tail_591_);
lean_dec(v_head_590_);
lean_dec(v_x_583_);
if (v_isShared_600_ == 0)
{
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_597_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_13402__boxed_623_; lean_object* v_res_624_; 
v___x_13402__boxed_623_ = lean_unbox(v___x_615_);
v_res_624_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_13402__boxed_623_, v_x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_x_627_);
return v___x_633_;
}
else
{
lean_object* v_head_634_; lean_object* v_tail_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_658_; 
v_head_634_ = lean_ctor_get(v_x_626_, 0);
v_tail_635_ = lean_ctor_get(v_x_626_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_658_ == 0)
{
v___x_637_ = v_x_626_;
v_isShared_638_ = v_isSharedCheck_658_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_tail_635_);
lean_inc(v_head_634_);
lean_dec(v_x_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_658_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_644_; 
lean_inc(v_head_634_);
v___x_644_ = l_Lean_MVarId_inferInstance(v_head_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_dec_ref_known(v___x_644_, 1);
if (v___x_625_ == 0)
{
lean_del_object(v___x_637_);
lean_dec(v_head_634_);
v_x_626_ = v_tail_635_;
goto _start;
}
else
{
goto v___jp_639_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_a_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_657_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___y_651_; uint8_t v___x_655_; 
v___x_655_ = l_Lean_Exception_isInterrupt(v_a_646_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
lean_inc(v_a_646_);
v___x_656_ = l_Lean_Exception_isRuntime(v_a_646_);
v___y_651_ = v___x_656_;
goto v___jp_650_;
}
else
{
v___y_651_ = v___x_655_;
goto v___jp_650_;
}
v___jp_650_:
{
if (v___y_651_ == 0)
{
lean_del_object(v___x_648_);
lean_dec(v_a_646_);
goto v___jp_639_;
}
else
{
lean_object* v___x_653_; 
lean_del_object(v___x_637_);
lean_dec(v_tail_635_);
lean_dec(v_head_634_);
lean_dec(v_x_627_);
if (v_isShared_649_ == 0)
{
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_646_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
v___jp_639_:
{
lean_object* v___x_641_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_x_627_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_head_634_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_x_627_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v_x_626_ = v_tail_635_;
v_x_627_ = v___x_641_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_13479__boxed_667_; lean_object* v_res_668_; 
v___x_13479__boxed_667_ = lean_unbox(v___x_659_);
v_res_668_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_13479__boxed_667_, v_x_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_668_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_672_; double v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(1000000000u);
v___x_673_ = lean_float_of_nat(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_674_, lean_object* v_g_675_, lean_object* v_e_676_, lean_object* v_cfg_677_, lean_object* v___x_678_, lean_object* v___x_679_, uint8_t v___x_680_, lean_object* v___x_681_, lean_object* v___f_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_options_688_; uint8_t v_hasTrace_689_; 
v_options_688_ = lean_ctor_get(v___y_685_, 2);
v_hasTrace_689_ = lean_ctor_get_uint8(v_options_688_, sizeof(void*)*1);
if (v_hasTrace_689_ == 0)
{
lean_object* v_keyedConfig_690_; uint8_t v_trackZetaDelta_691_; lean_object* v_zetaDeltaSet_692_; lean_object* v_lctx_693_; lean_object* v_localInstances_694_; lean_object* v_defEqCtx_x3f_695_; lean_object* v_synthPendingDepth_696_; lean_object* v_customCanUnfoldPredicate_x3f_697_; uint8_t v_univApprox_698_; uint8_t v_inTypeClassResolution_699_; uint8_t v_cacheInferType_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v_keyedConfig_690_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_691_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_692_ = lean_ctor_get(v___y_683_, 1);
v_lctx_693_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_694_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_695_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_696_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_697_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_698_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_699_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_700_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_690_);
v___x_701_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_690_);
lean_inc(v_customCanUnfoldPredicate_x3f_697_);
lean_inc(v_synthPendingDepth_696_);
lean_inc(v_defEqCtx_x3f_695_);
lean_inc_ref(v_localInstances_694_);
lean_inc_ref(v_lctx_693_);
lean_inc(v_zetaDeltaSet_692_);
v___x_702_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v_zetaDeltaSet_692_);
lean_ctor_set(v___x_702_, 2, v_lctx_693_);
lean_ctor_set(v___x_702_, 3, v_localInstances_694_);
lean_ctor_set(v___x_702_, 4, v_defEqCtx_x3f_695_);
lean_ctor_set(v___x_702_, 5, v_synthPendingDepth_696_);
lean_ctor_set(v___x_702_, 6, v_customCanUnfoldPredicate_x3f_697_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7, v_trackZetaDelta_691_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7 + 1, v_univApprox_698_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7 + 2, v_inTypeClassResolution_699_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*7 + 3, v_cacheInferType_700_);
v___x_703_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_702_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_702_, 7);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_box(0);
v___x_706_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_689_, v_a_704_, v___x_705_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_List_reverse___redArg(v_a_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
return v___x_706_;
}
}
else
{
lean_dec_ref(v___y_683_);
return v___x_703_;
}
}
else
{
lean_object* v_inheritedTraceOptions_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v_a_723_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v_a_738_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v_a_756_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v_a_768_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; 
v_inheritedTraceOptions_716_ = lean_ctor_get(v___y_685_, 13);
v___x_717_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_679_);
v___x_718_ = l_Lean_Name_append(v___x_717_, v___x_679_);
v___x_719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_716_, v_options_688_, v___x_718_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_Lean_trace_profiler;
v___x_829_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v_keyedConfig_830_; uint8_t v_trackZetaDelta_831_; lean_object* v_zetaDeltaSet_832_; lean_object* v_lctx_833_; lean_object* v_localInstances_834_; lean_object* v_defEqCtx_x3f_835_; lean_object* v_synthPendingDepth_836_; lean_object* v_customCanUnfoldPredicate_x3f_837_; uint8_t v_univApprox_838_; uint8_t v_inTypeClassResolution_839_; uint8_t v_cacheInferType_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v___f_682_);
lean_dec_ref(v___x_681_);
lean_dec(v___x_679_);
v_keyedConfig_830_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_831_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_832_ = lean_ctor_get(v___y_683_, 1);
v_lctx_833_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_834_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_835_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_836_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_837_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_838_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_839_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_840_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_830_);
v___x_841_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_830_);
lean_inc(v_customCanUnfoldPredicate_x3f_837_);
lean_inc(v_synthPendingDepth_836_);
lean_inc(v_defEqCtx_x3f_835_);
lean_inc_ref(v_localInstances_834_);
lean_inc_ref(v_lctx_833_);
lean_inc(v_zetaDeltaSet_832_);
v___x_842_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_zetaDeltaSet_832_);
lean_ctor_set(v___x_842_, 2, v_lctx_833_);
lean_ctor_set(v___x_842_, 3, v_localInstances_834_);
lean_ctor_set(v___x_842_, 4, v_defEqCtx_x3f_835_);
lean_ctor_set(v___x_842_, 5, v_synthPendingDepth_836_);
lean_ctor_set(v___x_842_, 6, v_customCanUnfoldPredicate_x3f_837_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7, v_trackZetaDelta_831_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7 + 1, v_univApprox_838_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7 + 2, v_inTypeClassResolution_839_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*7 + 3, v_cacheInferType_840_);
v___x_843_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_842_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_842_, 7);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = lean_box(0);
v___x_846_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_829_, v_hasTrace_689_, v_a_844_, v___x_845_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_855_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = l_List_reverse___redArg(v_a_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
return v___x_846_;
}
}
else
{
lean_dec_ref(v___y_683_);
return v___x_843_;
}
}
else
{
goto v___jp_783_;
}
}
else
{
goto v___jp_783_;
}
v___jp_720_:
{
lean_object* v___x_724_; double v___x_725_; double v___x_726_; double v___x_727_; double v___x_728_; double v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_724_ = lean_io_mono_nanos_now();
v___x_725_ = lean_float_of_nat(v___y_722_);
v___x_726_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_727_ = lean_float_div(v___x_725_, v___x_726_);
v___x_728_ = lean_float_of_nat(v___x_724_);
v___x_729_ = lean_float_div(v___x_728_, v___x_726_);
v___x_730_ = lean_box_float(v___x_727_);
v___x_731_ = lean_box_float(v___x_729_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_723_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_719_, v___y_721_, v___f_682_, v___x_733_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
return v___x_734_;
}
v___jp_735_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_a_738_);
v___y_721_ = v___y_736_;
v___y_722_ = v___y_737_;
v_a_723_ = v___x_739_;
goto v___jp_720_;
}
v___jp_740_:
{
if (lean_obj_tag(v___y_743_) == 0)
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v___y_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___y_743_, 1);
v___y_736_ = v___y_741_;
v___y_737_ = v___y_742_;
v_a_738_ = v_a_744_;
goto v___jp_735_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___y_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___y_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___y_743_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___y_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v___y_721_ = v___y_741_;
v___y_722_ = v___y_742_;
v_a_723_ = v___x_750_;
goto v___jp_720_;
}
}
}
}
v___jp_753_:
{
lean_object* v___x_757_; double v___x_758_; double v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_757_ = lean_io_get_num_heartbeats();
v___x_758_ = lean_float_of_nat(v___y_754_);
v___x_759_ = lean_float_of_nat(v___x_757_);
v___x_760_ = lean_box_float(v___x_758_);
v___x_761_ = lean_box_float(v___x_759_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_a_756_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_679_, v___x_680_, v___x_681_, v_options_688_, v___x_719_, v___y_755_, v___f_682_, v___x_763_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_683_);
return v___x_764_;
}
v___jp_765_:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_a_768_);
v___y_754_ = v___y_766_;
v___y_755_ = v___y_767_;
v_a_756_ = v___x_769_;
goto v___jp_753_;
}
v___jp_770_:
{
if (lean_obj_tag(v___y_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___y_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___y_773_, 1);
v___y_766_ = v___y_771_;
v___y_767_ = v___y_772_;
v_a_768_ = v_a_774_;
goto v___jp_765_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___y_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___y_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___y_773_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___y_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 0);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
v___y_754_ = v___y_771_;
v___y_755_ = v___y_772_;
v_a_756_ = v___x_780_;
goto v___jp_753_;
}
}
}
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_686_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v___x_786_ = l_Lean_trace_profiler_useHeartbeats;
v___x_787_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_688_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v_keyedConfig_789_; uint8_t v_trackZetaDelta_790_; lean_object* v_zetaDeltaSet_791_; lean_object* v_lctx_792_; lean_object* v_localInstances_793_; lean_object* v_defEqCtx_x3f_794_; lean_object* v_synthPendingDepth_795_; lean_object* v_customCanUnfoldPredicate_x3f_796_; uint8_t v_univApprox_797_; uint8_t v_inTypeClassResolution_798_; uint8_t v_cacheInferType_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_788_ = lean_io_mono_nanos_now();
v_keyedConfig_789_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_790_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_791_ = lean_ctor_get(v___y_683_, 1);
v_lctx_792_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_793_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_794_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_795_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_796_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_797_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_798_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_799_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_789_);
v___x_800_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_789_);
lean_inc(v_customCanUnfoldPredicate_x3f_796_);
lean_inc(v_synthPendingDepth_795_);
lean_inc(v_defEqCtx_x3f_794_);
lean_inc_ref(v_localInstances_793_);
lean_inc_ref(v_lctx_792_);
lean_inc(v_zetaDeltaSet_791_);
v___x_801_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_zetaDeltaSet_791_);
lean_ctor_set(v___x_801_, 2, v_lctx_792_);
lean_ctor_set(v___x_801_, 3, v_localInstances_793_);
lean_ctor_set(v___x_801_, 4, v_defEqCtx_x3f_794_);
lean_ctor_set(v___x_801_, 5, v_synthPendingDepth_795_);
lean_ctor_set(v___x_801_, 6, v_customCanUnfoldPredicate_x3f_796_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7, v_trackZetaDelta_790_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7 + 1, v_univApprox_797_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7 + 2, v_inTypeClassResolution_798_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*7 + 3, v_cacheInferType_799_);
v___x_802_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_801_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_801_, 7);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_box(0);
v___x_805_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_787_, v_hasTrace_689_, v_a_803_, v___x_804_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = l_List_reverse___redArg(v_a_806_);
v___y_736_ = v_a_785_;
v___y_737_ = v___x_788_;
v_a_738_ = v___x_807_;
goto v___jp_735_;
}
else
{
v___y_741_ = v_a_785_;
v___y_742_ = v___x_788_;
v___y_743_ = v___x_805_;
goto v___jp_740_;
}
}
else
{
v___y_741_ = v_a_785_;
v___y_742_ = v___x_788_;
v___y_743_ = v___x_802_;
goto v___jp_740_;
}
}
else
{
lean_object* v___x_808_; lean_object* v_keyedConfig_809_; uint8_t v_trackZetaDelta_810_; lean_object* v_zetaDeltaSet_811_; lean_object* v_lctx_812_; lean_object* v_localInstances_813_; lean_object* v_defEqCtx_x3f_814_; lean_object* v_synthPendingDepth_815_; lean_object* v_customCanUnfoldPredicate_x3f_816_; uint8_t v_univApprox_817_; uint8_t v_inTypeClassResolution_818_; uint8_t v_cacheInferType_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_808_ = lean_io_get_num_heartbeats();
v_keyedConfig_809_ = lean_ctor_get(v___y_683_, 0);
v_trackZetaDelta_810_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7);
v_zetaDeltaSet_811_ = lean_ctor_get(v___y_683_, 1);
v_lctx_812_ = lean_ctor_get(v___y_683_, 2);
v_localInstances_813_ = lean_ctor_get(v___y_683_, 3);
v_defEqCtx_x3f_814_ = lean_ctor_get(v___y_683_, 4);
v_synthPendingDepth_815_ = lean_ctor_get(v___y_683_, 5);
v_customCanUnfoldPredicate_x3f_816_ = lean_ctor_get(v___y_683_, 6);
v_univApprox_817_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_818_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 2);
v_cacheInferType_819_ = lean_ctor_get_uint8(v___y_683_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_809_);
v___x_820_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_transparency_674_, v_keyedConfig_809_);
lean_inc(v_customCanUnfoldPredicate_x3f_816_);
lean_inc(v_synthPendingDepth_815_);
lean_inc(v_defEqCtx_x3f_814_);
lean_inc_ref(v_localInstances_813_);
lean_inc_ref(v_lctx_812_);
lean_inc(v_zetaDeltaSet_811_);
v___x_821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_zetaDeltaSet_811_);
lean_ctor_set(v___x_821_, 2, v_lctx_812_);
lean_ctor_set(v___x_821_, 3, v_localInstances_813_);
lean_ctor_set(v___x_821_, 4, v_defEqCtx_x3f_814_);
lean_ctor_set(v___x_821_, 5, v_synthPendingDepth_815_);
lean_ctor_set(v___x_821_, 6, v_customCanUnfoldPredicate_x3f_816_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7, v_trackZetaDelta_810_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7 + 1, v_univApprox_817_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7 + 2, v_inTypeClassResolution_818_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*7 + 3, v_cacheInferType_819_);
v___x_822_ = l_Lean_MVarId_apply(v_g_675_, v_e_676_, v_cfg_677_, v___x_678_, v___x_821_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref_known(v___x_821_, 7);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_box(0);
v___x_825_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_787_, v_a_823_, v___x_824_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_List_reverse___redArg(v_a_826_);
v___y_766_ = v___x_808_;
v___y_767_ = v_a_785_;
v_a_768_ = v___x_827_;
goto v___jp_765_;
}
else
{
v___y_771_ = v___x_808_;
v___y_772_ = v_a_785_;
v___y_773_ = v___x_825_;
goto v___jp_770_;
}
}
else
{
v___y_771_ = v___x_808_;
v___y_772_ = v_a_785_;
v___y_773_ = v___x_822_;
goto v___jp_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_856_, lean_object* v_g_857_, lean_object* v_e_858_, lean_object* v_cfg_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v___f_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_transparency_boxed_870_; uint8_t v___x_13567__boxed_871_; lean_object* v_res_872_; 
v_transparency_boxed_870_ = lean_unbox(v_transparency_856_);
v___x_13567__boxed_871_ = lean_unbox(v___x_862_);
v_res_872_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_870_, v_g_857_, v_e_858_, v_cfg_859_, v___x_860_, v___x_861_, v___x_13567__boxed_871_, v___x_863_, v___f_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_874_, lean_object* v_g_875_, lean_object* v_cfg_876_, lean_object* v_e_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
lean_inc_ref(v_e_877_);
v___f_883_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_883_, 0, v_e_877_);
v___x_884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_885_ = lean_box(0);
v___x_886_ = 1;
v___x_887_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_888_ = lean_box(v_transparency_874_);
v___x_889_ = lean_box(v___x_886_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_890_, 0, v___x_888_);
lean_closure_set(v___f_890_, 1, v_g_875_);
lean_closure_set(v___f_890_, 2, v_e_877_);
lean_closure_set(v___f_890_, 3, v_cfg_876_);
lean_closure_set(v___f_890_, 4, v___x_885_);
lean_closure_set(v___f_890_, 5, v___x_884_);
lean_closure_set(v___f_890_, 6, v___x_889_);
lean_closure_set(v___f_890_, 7, v___x_887_);
lean_closure_set(v___f_890_, 8, v___f_883_);
v___x_891_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_890_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_892_, lean_object* v_g_893_, lean_object* v_cfg_894_, lean_object* v_e_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v_transparency_boxed_901_; lean_object* v_res_902_; 
v_transparency_boxed_901_ = lean_unbox(v_transparency_892_);
v_res_902_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_901_, v_g_893_, v_cfg_894_, v_e_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_903_, uint8_t v_transparency_904_, lean_object* v_lemmas_905_, lean_object* v_g_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_905_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_921_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_921_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_915_ = lean_box(v_transparency_904_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_916_, 0, v___x_915_);
lean_closure_set(v___f_916_, 1, v_g_906_);
lean_closure_set(v___f_916_, 2, v_cfg_903_);
v___x_917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_917_, 0, lean_box(0));
lean_closure_set(v___x_917_, 1, lean_box(0));
lean_closure_set(v___x_917_, 2, v___f_916_);
lean_closure_set(v___x_917_, 3, v_a_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_917_);
v___x_919_ = v___x_913_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_g_906_);
lean_dec_ref(v_cfg_903_);
v_a_922_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_910_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_910_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_930_, lean_object* v_transparency_931_, lean_object* v_lemmas_932_, lean_object* v_g_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_transparency_boxed_937_; lean_object* v_res_938_; 
v_transparency_boxed_937_ = lean_unbox(v_transparency_931_);
v_res_938_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_930_, v_transparency_boxed_937_, v_lemmas_932_, v_g_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec(v_a_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_939_, uint8_t v_transparency_940_, lean_object* v_lemmas_941_, lean_object* v_g_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_939_, v_transparency_940_, v_lemmas_941_, v_g_942_, v_a_944_, v_a_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_949_, lean_object* v_transparency_950_, lean_object* v_lemmas_951_, lean_object* v_g_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
uint8_t v_transparency_boxed_958_; lean_object* v_res_959_; 
v_transparency_boxed_958_ = lean_unbox(v_transparency_950_);
v_res_959_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_949_, v_transparency_boxed_958_, v_lemmas_951_, v_g_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_00_u03b1_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___redArg(v_x_961_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_00_u03b1_968_, lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_00_u03b1_968_, v_x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_976_, uint8_t v_transparency_977_, lean_object* v_lemmas_978_, lean_object* v_g_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_976_, v_transparency_977_, v_lemmas_978_, v_g_979_, v_a_981_, v_a_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_Meta_Iterator_head___redArg(v_a_986_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_987_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_985_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_985_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_996_, lean_object* v_transparency_997_, lean_object* v_lemmas_998_, lean_object* v_g_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
uint8_t v_transparency_boxed_1005_; lean_object* v_res_1006_; 
v_transparency_boxed_1005_ = lean_unbox(v_transparency_997_);
v_res_1006_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_996_, v_transparency_boxed_1005_, v_lemmas_998_, v_g_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1007_){
_start:
{
lean_object* v_toApplyRulesConfig_1008_; lean_object* v_toBacktrackConfig_1009_; 
v_toApplyRulesConfig_1008_ = lean_ctor_get(v_x_1007_, 0);
v_toBacktrackConfig_1009_ = lean_ctor_get(v_toApplyRulesConfig_1008_, 0);
lean_inc_ref(v_toBacktrackConfig_1009_);
return v_toBacktrackConfig_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1010_);
lean_dec_ref(v_x_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1014_, lean_object* v_discharge_1015_, lean_object* v_g_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v_g_1016_);
v___x_1022_ = lean_apply_6(v_test_1014_, v_g_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1033_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1033_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1033_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_unbox(v_a_1023_);
lean_dec(v_a_1023_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
lean_del_object(v___x_1025_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
v___x_1028_ = lean_apply_6(v_discharge_1015_, v_g_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec(v_g_1016_);
lean_dec_ref(v_discharge_1015_);
v___x_1029_ = lean_box(0);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v_g_1016_);
lean_dec_ref(v_discharge_1015_);
v_a_1034_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1022_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1022_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1042_, lean_object* v_discharge_1043_, lean_object* v_g_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1042_, v_discharge_1043_, v_g_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1051_, lean_object* v_test_1052_){
_start:
{
lean_object* v_toApplyRulesConfig_1053_; lean_object* v_toBacktrackConfig_1054_; uint8_t v_backtracking_1055_; uint8_t v_intro_1056_; uint8_t v_constructor_1057_; uint8_t v_suggestions_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1090_; 
v_toApplyRulesConfig_1053_ = lean_ctor_get(v_cfg_1051_, 0);
lean_inc_ref(v_toApplyRulesConfig_1053_);
v_toBacktrackConfig_1054_ = lean_ctor_get(v_toApplyRulesConfig_1053_, 0);
lean_inc_ref(v_toBacktrackConfig_1054_);
v_backtracking_1055_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1);
v_intro_1056_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1 + 1);
v_constructor_1057_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1 + 2);
v_suggestions_1058_ = lean_ctor_get_uint8(v_cfg_1051_, sizeof(void*)*1 + 3);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_cfg_1051_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_cfg_1051_, 0);
lean_dec(v_unused_1091_);
v___x_1060_ = v_cfg_1051_;
v_isShared_1061_ = v_isSharedCheck_1090_;
goto v_resetjp_1059_;
}
else
{
lean_dec(v_cfg_1051_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1090_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_toApplyConfig_1062_; uint8_t v_transparency_1063_; uint8_t v_symm_1064_; uint8_t v_exfalso_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1088_; 
v_toApplyConfig_1062_ = lean_ctor_get(v_toApplyRulesConfig_1053_, 1);
v_transparency_1063_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1053_, sizeof(void*)*2);
v_symm_1064_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1053_, sizeof(void*)*2 + 1);
v_exfalso_1065_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1053_, sizeof(void*)*2 + 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_toApplyRulesConfig_1053_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_toApplyRulesConfig_1053_, 0);
lean_dec(v_unused_1089_);
v___x_1067_ = v_toApplyRulesConfig_1053_;
v_isShared_1068_ = v_isSharedCheck_1088_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_toApplyConfig_1062_);
lean_dec(v_toApplyRulesConfig_1053_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1088_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_maxDepth_1069_; lean_object* v_proc_1070_; lean_object* v_suspend_1071_; lean_object* v_discharge_1072_; uint8_t v_commitIndependentGoals_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1087_; 
v_maxDepth_1069_ = lean_ctor_get(v_toBacktrackConfig_1054_, 0);
v_proc_1070_ = lean_ctor_get(v_toBacktrackConfig_1054_, 1);
v_suspend_1071_ = lean_ctor_get(v_toBacktrackConfig_1054_, 2);
v_discharge_1072_ = lean_ctor_get(v_toBacktrackConfig_1054_, 3);
v_commitIndependentGoals_1073_ = lean_ctor_get_uint8(v_toBacktrackConfig_1054_, sizeof(void*)*4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_toBacktrackConfig_1054_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1075_ = v_toBacktrackConfig_1054_;
v_isShared_1076_ = v_isSharedCheck_1087_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_discharge_1072_);
lean_inc(v_suspend_1071_);
lean_inc(v_proc_1070_);
lean_inc(v_maxDepth_1069_);
lean_dec(v_toBacktrackConfig_1054_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1087_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___f_1077_; lean_object* v___x_1079_; 
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1077_, 0, v_test_1052_);
lean_closure_set(v___f_1077_, 1, v_discharge_1072_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 3, v___f_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_maxDepth_1069_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_proc_1070_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_suspend_1071_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___f_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1086_, sizeof(void*)*4, v_commitIndependentGoals_1073_);
v___x_1079_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1079_);
v___x_1081_ = v___x_1067_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_toApplyConfig_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2, v_transparency_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2 + 1, v_symm_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2 + 2, v_exfalso_1065_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1081_);
v___x_1083_ = v___x_1060_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1, v_backtracking_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1 + 1, v_intro_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1 + 2, v_constructor_1057_);
lean_ctor_set_uint8(v_reuseFailAlloc_1084_, sizeof(void*)*1 + 3, v_suggestions_1058_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1092_, lean_object* v_proc_1093_, lean_object* v_orig_1094_, lean_object* v_goals_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
if (lean_obj_tag(v_goals_1095_) == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref(v_proc_1093_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
v___x_1101_ = lean_apply_7(v_proc_1092_, v_orig_1094_, v_goals_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
return v___x_1101_;
}
else
{
lean_object* v_head_1102_; lean_object* v_tail_1103_; lean_object* v___x_1104_; 
v_head_1102_ = lean_ctor_get(v_goals_1095_, 0);
v_tail_1103_ = lean_ctor_get(v_goals_1095_, 1);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v_head_1102_);
v___x_1104_ = lean_apply_6(v_proc_1093_, v_head_1102_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
lean_inc(v_tail_1103_);
lean_dec_ref_known(v_goals_1095_, 2);
lean_dec(v_orig_1094_);
lean_dec_ref(v_proc_1092_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = l_List_appendTR___redArg(v_a_1105_, v_tail_1103_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1110_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1127_; 
v_a_1115_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1117_ = v___x_1104_;
v_isShared_1118_ = v_isSharedCheck_1127_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1104_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1127_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___y_1120_; uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_Exception_isInterrupt(v_a_1115_);
if (v___x_1125_ == 0)
{
uint8_t v___x_1126_; 
lean_inc(v_a_1115_);
v___x_1126_ = l_Lean_Exception_isRuntime(v_a_1115_);
v___y_1120_ = v___x_1126_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v___x_1125_;
goto v___jp_1119_;
}
v___jp_1119_:
{
if (v___y_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_del_object(v___x_1117_);
lean_dec(v_a_1115_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
v___x_1121_ = lean_apply_7(v_proc_1092_, v_orig_1094_, v_goals_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, lean_box(0));
return v___x_1121_;
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref_known(v_goals_1095_, 2);
lean_dec(v_orig_1094_);
lean_dec_ref(v_proc_1092_);
if (v_isShared_1118_ == 0)
{
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1115_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1128_, lean_object* v_proc_1129_, lean_object* v_orig_1130_, lean_object* v_goals_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1128_, v_proc_1129_, v_orig_1130_, v_goals_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1138_, lean_object* v_proc_1139_){
_start:
{
lean_object* v_toApplyRulesConfig_1140_; lean_object* v_toBacktrackConfig_1141_; uint8_t v_backtracking_1142_; uint8_t v_intro_1143_; uint8_t v_constructor_1144_; uint8_t v_suggestions_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1177_; 
v_toApplyRulesConfig_1140_ = lean_ctor_get(v_cfg_1138_, 0);
lean_inc_ref(v_toApplyRulesConfig_1140_);
v_toBacktrackConfig_1141_ = lean_ctor_get(v_toApplyRulesConfig_1140_, 0);
lean_inc_ref(v_toBacktrackConfig_1141_);
v_backtracking_1142_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1);
v_intro_1143_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1 + 1);
v_constructor_1144_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1 + 2);
v_suggestions_1145_ = lean_ctor_get_uint8(v_cfg_1138_, sizeof(void*)*1 + 3);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_cfg_1138_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; 
v_unused_1178_ = lean_ctor_get(v_cfg_1138_, 0);
lean_dec(v_unused_1178_);
v___x_1147_ = v_cfg_1138_;
v_isShared_1148_ = v_isSharedCheck_1177_;
goto v_resetjp_1146_;
}
else
{
lean_dec(v_cfg_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1177_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_toApplyConfig_1149_; uint8_t v_transparency_1150_; uint8_t v_symm_1151_; uint8_t v_exfalso_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1175_; 
v_toApplyConfig_1149_ = lean_ctor_get(v_toApplyRulesConfig_1140_, 1);
v_transparency_1150_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1140_, sizeof(void*)*2);
v_symm_1151_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1140_, sizeof(void*)*2 + 1);
v_exfalso_1152_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1140_, sizeof(void*)*2 + 2);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_toApplyRulesConfig_1140_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_toApplyRulesConfig_1140_, 0);
lean_dec(v_unused_1176_);
v___x_1154_ = v_toApplyRulesConfig_1140_;
v_isShared_1155_ = v_isSharedCheck_1175_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_toApplyConfig_1149_);
lean_dec(v_toApplyRulesConfig_1140_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1175_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_maxDepth_1156_; lean_object* v_proc_1157_; lean_object* v_suspend_1158_; lean_object* v_discharge_1159_; uint8_t v_commitIndependentGoals_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1174_; 
v_maxDepth_1156_ = lean_ctor_get(v_toBacktrackConfig_1141_, 0);
v_proc_1157_ = lean_ctor_get(v_toBacktrackConfig_1141_, 1);
v_suspend_1158_ = lean_ctor_get(v_toBacktrackConfig_1141_, 2);
v_discharge_1159_ = lean_ctor_get(v_toBacktrackConfig_1141_, 3);
v_commitIndependentGoals_1160_ = lean_ctor_get_uint8(v_toBacktrackConfig_1141_, sizeof(void*)*4);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_toBacktrackConfig_1141_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1162_ = v_toBacktrackConfig_1141_;
v_isShared_1163_ = v_isSharedCheck_1174_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_discharge_1159_);
lean_inc(v_suspend_1158_);
lean_inc(v_proc_1157_);
lean_inc(v_maxDepth_1156_);
lean_dec(v_toBacktrackConfig_1141_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1174_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___f_1164_; lean_object* v___x_1166_; 
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1164_, 0, v_proc_1157_);
lean_closure_set(v___f_1164_, 1, v_proc_1139_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___f_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_maxDepth_1156_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___f_1164_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_suspend_1158_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_discharge_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1173_, sizeof(void*)*4, v_commitIndependentGoals_1160_);
v___x_1166_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1166_);
v___x_1168_ = v___x_1154_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_toApplyConfig_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2, v_transparency_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2 + 1, v_symm_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1172_, sizeof(void*)*2 + 2, v_exfalso_1152_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1168_);
v___x_1170_ = v___x_1147_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1, v_backtracking_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1 + 1, v_intro_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1 + 2, v_constructor_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*1 + 3, v_suggestions_1145_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = 1;
v___x_1186_ = l_Lean_Meta_intro1Core(v_g_1179_, v___x_1185_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1204_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1204_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1204_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_snd_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1202_; 
v_snd_1191_ = lean_ctor_get(v_a_1187_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_a_1187_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_a_1187_, 0);
lean_dec(v_unused_1203_);
v___x_1193_ = v_a_1187_;
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_snd_1191_);
lean_dec(v_a_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1202_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(0);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 1);
lean_ctor_set(v___x_1193_, 1, v___x_1195_);
lean_ctor_set(v___x_1193_, 0, v_snd_1191_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_snd_1191_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1197_);
v___x_1199_ = v___x_1189_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1186_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1186_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1221_){
_start:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; 
v___f_1222_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1223_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1221_, v___f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1224_, lean_object* v_x_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_ks_1228_; lean_object* v_vs_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1253_; 
v_ks_1228_ = lean_ctor_get(v_x_1224_, 0);
v_vs_1229_ = lean_ctor_get(v_x_1224_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1224_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1231_ = v_x_1224_;
v_isShared_1232_ = v_isSharedCheck_1253_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_vs_1229_);
lean_inc(v_ks_1228_);
lean_dec(v_x_1224_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1253_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_ks_1228_);
v___x_1234_ = lean_nat_dec_lt(v_x_1225_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v_x_1225_);
v___x_1235_ = lean_array_push(v_ks_1228_, v_x_1226_);
v___x_1236_ = lean_array_push(v_vs_1229_, v_x_1227_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1236_);
lean_ctor_set(v___x_1231_, 0, v___x_1235_);
v___x_1238_ = v___x_1231_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v_k_x27_1240_; uint8_t v___x_1241_; 
v_k_x27_1240_ = lean_array_fget_borrowed(v_ks_1228_, v_x_1225_);
v___x_1241_ = l_Lean_instBEqMVarId_beq(v_x_1226_, v_k_x27_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1243_; 
if (v_isShared_1232_ == 0)
{
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ks_1228_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_vs_1229_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_x_1225_, v___x_1244_);
lean_dec(v_x_1225_);
v_x_1224_ = v___x_1243_;
v_x_1225_ = v___x_1245_;
goto _start;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1248_ = lean_array_fset(v_ks_1228_, v_x_1225_, v_x_1226_);
v___x_1249_ = lean_array_fset(v_vs_1229_, v_x_1225_, v_x_1227_);
lean_dec(v_x_1225_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1249_);
lean_ctor_set(v___x_1231_, 0, v___x_1248_);
v___x_1251_ = v___x_1231_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1254_, lean_object* v_k_1255_, lean_object* v_v_1256_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1254_, v___x_1257_, v_k_1255_, v_v_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1260_, size_t v_x_1261_, size_t v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
lean_object* v_es_1265_; size_t v___x_1266_; size_t v___x_1267_; lean_object* v_j_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_es_1265_ = lean_ctor_get(v_x_1260_, 0);
v___x_1266_ = ((size_t)31ULL);
v___x_1267_ = lean_usize_land(v_x_1261_, v___x_1266_);
v_j_1268_ = lean_usize_to_nat(v___x_1267_);
v___x_1269_ = lean_array_get_size(v_es_1265_);
v___x_1270_ = lean_nat_dec_lt(v_j_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v_j_1268_);
lean_dec(v_x_1264_);
lean_dec(v_x_1263_);
return v_x_1260_;
}
else
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1309_; 
lean_inc_ref(v_es_1265_);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_x_1260_, 0);
lean_dec(v_unused_1310_);
v___x_1272_ = v_x_1260_;
v_isShared_1273_ = v_isSharedCheck_1309_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_x_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1309_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_v_1274_; lean_object* v___x_1275_; lean_object* v_xs_x27_1276_; lean_object* v___y_1278_; 
v_v_1274_ = lean_array_fget(v_es_1265_, v_j_1268_);
v___x_1275_ = lean_box(0);
v_xs_x27_1276_ = lean_array_fset(v_es_1265_, v_j_1268_, v___x_1275_);
switch(lean_obj_tag(v_v_1274_))
{
case 0:
{
lean_object* v_key_1283_; lean_object* v_val_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1294_; 
v_key_1283_ = lean_ctor_get(v_v_1274_, 0);
v_val_1284_ = lean_ctor_get(v_v_1274_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_v_1274_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1286_ = v_v_1274_;
v_isShared_1287_ = v_isSharedCheck_1294_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_val_1284_);
lean_inc(v_key_1283_);
lean_dec(v_v_1274_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1294_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_instBEqMVarId_beq(v_x_1263_, v_key_1283_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_del_object(v___x_1286_);
v___x_1289_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1283_, v_val_1284_, v_x_1263_, v_x_1264_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
v___y_1278_ = v___x_1290_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1292_; 
lean_dec(v_val_1284_);
lean_dec(v_key_1283_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v_x_1264_);
lean_ctor_set(v___x_1286_, 0, v_x_1263_);
v___x_1292_ = v___x_1286_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_x_1263_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_x_1264_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
v___y_1278_ = v___x_1292_;
goto v___jp_1277_;
}
}
}
}
case 1:
{
lean_object* v_node_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1307_; 
v_node_1295_ = lean_ctor_get(v_v_1274_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_v_1274_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1297_ = v_v_1274_;
v_isShared_1298_ = v_isSharedCheck_1307_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_node_1295_);
lean_dec(v_v_1274_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1307_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1299_ = ((size_t)5ULL);
v___x_1300_ = lean_usize_shift_right(v_x_1261_, v___x_1299_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_x_1262_, v___x_1301_);
v___x_1303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1295_, v___x_1300_, v___x_1302_, v_x_1263_, v_x_1264_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1303_);
v___x_1305_ = v___x_1297_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v___y_1278_ = v___x_1305_;
goto v___jp_1277_;
}
}
}
default: 
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_x_1263_);
lean_ctor_set(v___x_1308_, 1, v_x_1264_);
v___y_1278_ = v___x_1308_;
goto v___jp_1277_;
}
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_array_fset(v_xs_x27_1276_, v_j_1268_, v___y_1278_);
lean_dec(v_j_1268_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1279_);
v___x_1281_ = v___x_1272_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v_ks_1311_; lean_object* v_vs_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1332_; 
v_ks_1311_ = lean_ctor_get(v_x_1260_, 0);
v_vs_1312_ = lean_ctor_get(v_x_1260_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1260_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1314_ = v_x_1260_;
v_isShared_1315_ = v_isSharedCheck_1332_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_vs_1312_);
lean_inc(v_ks_1311_);
lean_dec(v_x_1260_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1332_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_ks_1311_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_vs_1312_);
v___x_1317_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v_newNode_1318_; uint8_t v___y_1320_; size_t v___x_1326_; uint8_t v___x_1327_; 
v_newNode_1318_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1317_, v_x_1263_, v_x_1264_);
v___x_1326_ = ((size_t)7ULL);
v___x_1327_ = lean_usize_dec_le(v___x_1326_, v_x_1262_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1318_);
v___x_1329_ = lean_unsigned_to_nat(4u);
v___x_1330_ = lean_nat_dec_lt(v___x_1328_, v___x_1329_);
lean_dec(v___x_1328_);
v___y_1320_ = v___x_1330_;
goto v___jp_1319_;
}
else
{
v___y_1320_ = v___x_1327_;
goto v___jp_1319_;
}
v___jp_1319_:
{
if (v___y_1320_ == 0)
{
lean_object* v_ks_1321_; lean_object* v_vs_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_ks_1321_ = lean_ctor_get(v_newNode_1318_, 0);
lean_inc_ref(v_ks_1321_);
v_vs_1322_ = lean_ctor_get(v_newNode_1318_, 1);
lean_inc_ref(v_vs_1322_);
lean_dec_ref(v_newNode_1318_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1262_, v_ks_1321_, v_vs_1322_, v___x_1323_, v___x_1324_);
lean_dec_ref(v_vs_1322_);
lean_dec_ref(v_ks_1321_);
return v___x_1325_;
}
else
{
return v_newNode_1318_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1333_, lean_object* v_keys_1334_, lean_object* v_vals_1335_, lean_object* v_i_1336_, lean_object* v_entries_1337_){
_start:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = lean_array_get_size(v_keys_1334_);
v___x_1339_ = lean_nat_dec_lt(v_i_1336_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v_i_1336_);
return v_entries_1337_;
}
else
{
lean_object* v_k_1340_; lean_object* v_v_1341_; uint64_t v___x_1342_; size_t v_h_1343_; size_t v___x_1344_; lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; size_t v_h_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_k_1340_ = lean_array_fget_borrowed(v_keys_1334_, v_i_1336_);
v_v_1341_ = lean_array_fget_borrowed(v_vals_1335_, v_i_1336_);
v___x_1342_ = l_Lean_instHashableMVarId_hash(v_k_1340_);
v_h_1343_ = lean_uint64_to_usize(v___x_1342_);
v___x_1344_ = ((size_t)5ULL);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_sub(v_depth_1333_, v___x_1346_);
v___x_1348_ = lean_usize_mul(v___x_1344_, v___x_1347_);
v_h_1349_ = lean_usize_shift_right(v_h_1343_, v___x_1348_);
v___x_1350_ = lean_nat_add(v_i_1336_, v___x_1345_);
lean_dec(v_i_1336_);
lean_inc(v_v_1341_);
lean_inc(v_k_1340_);
v___x_1351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1337_, v_h_1349_, v_depth_1333_, v_k_1340_, v_v_1341_);
v_i_1336_ = v___x_1350_;
v_entries_1337_ = v___x_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1353_, lean_object* v_keys_1354_, lean_object* v_vals_1355_, lean_object* v_i_1356_, lean_object* v_entries_1357_){
_start:
{
size_t v_depth_boxed_1358_; lean_object* v_res_1359_; 
v_depth_boxed_1358_ = lean_unbox_usize(v_depth_1353_);
lean_dec(v_depth_1353_);
v_res_1359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1358_, v_keys_1354_, v_vals_1355_, v_i_1356_, v_entries_1357_);
lean_dec_ref(v_vals_1355_);
lean_dec_ref(v_keys_1354_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
size_t v_x_824__boxed_1365_; size_t v_x_825__boxed_1366_; lean_object* v_res_1367_; 
v_x_824__boxed_1365_ = lean_unbox_usize(v_x_1361_);
lean_dec(v_x_1361_);
v_x_825__boxed_1366_ = lean_unbox_usize(v_x_1362_);
lean_dec(v_x_1362_);
v_res_1367_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1360_, v_x_824__boxed_1365_, v_x_825__boxed_1366_, v_x_1363_, v_x_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
uint64_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = l_Lean_instHashableMVarId_hash(v_x_1369_);
v___x_1372_ = lean_uint64_to_usize(v___x_1371_);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1368_, v___x_1372_, v___x_1373_, v_x_1369_, v_x_1370_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1375_, lean_object* v_val_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_mctx_1380_; lean_object* v_cache_1381_; lean_object* v_zetaDeltaFVarIds_1382_; lean_object* v_postponed_1383_; lean_object* v_diag_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1412_; 
v___x_1379_ = lean_st_ref_take(v___y_1377_);
v_mctx_1380_ = lean_ctor_get(v___x_1379_, 0);
v_cache_1381_ = lean_ctor_get(v___x_1379_, 1);
v_zetaDeltaFVarIds_1382_ = lean_ctor_get(v___x_1379_, 2);
v_postponed_1383_ = lean_ctor_get(v___x_1379_, 3);
v_diag_1384_ = lean_ctor_get(v___x_1379_, 4);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1386_ = v___x_1379_;
v_isShared_1387_ = v_isSharedCheck_1412_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_diag_1384_);
lean_inc(v_postponed_1383_);
lean_inc(v_zetaDeltaFVarIds_1382_);
lean_inc(v_cache_1381_);
lean_inc(v_mctx_1380_);
lean_dec(v___x_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1412_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_depth_1388_; lean_object* v_levelAssignDepth_1389_; lean_object* v_lmvarCounter_1390_; lean_object* v_mvarCounter_1391_; lean_object* v_lDecls_1392_; lean_object* v_decls_1393_; lean_object* v_userNames_1394_; lean_object* v_lAssignment_1395_; lean_object* v_eAssignment_1396_; lean_object* v_dAssignment_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1411_; 
v_depth_1388_ = lean_ctor_get(v_mctx_1380_, 0);
v_levelAssignDepth_1389_ = lean_ctor_get(v_mctx_1380_, 1);
v_lmvarCounter_1390_ = lean_ctor_get(v_mctx_1380_, 2);
v_mvarCounter_1391_ = lean_ctor_get(v_mctx_1380_, 3);
v_lDecls_1392_ = lean_ctor_get(v_mctx_1380_, 4);
v_decls_1393_ = lean_ctor_get(v_mctx_1380_, 5);
v_userNames_1394_ = lean_ctor_get(v_mctx_1380_, 6);
v_lAssignment_1395_ = lean_ctor_get(v_mctx_1380_, 7);
v_eAssignment_1396_ = lean_ctor_get(v_mctx_1380_, 8);
v_dAssignment_1397_ = lean_ctor_get(v_mctx_1380_, 9);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_mctx_1380_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1399_ = v_mctx_1380_;
v_isShared_1400_ = v_isSharedCheck_1411_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_dAssignment_1397_);
lean_inc(v_eAssignment_1396_);
lean_inc(v_lAssignment_1395_);
lean_inc(v_userNames_1394_);
lean_inc(v_decls_1393_);
lean_inc(v_lDecls_1392_);
lean_inc(v_mvarCounter_1391_);
lean_inc(v_lmvarCounter_1390_);
lean_inc(v_levelAssignDepth_1389_);
lean_inc(v_depth_1388_);
lean_dec(v_mctx_1380_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1411_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1396_, v_mvarId_1375_, v_val_1376_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 8, v___x_1401_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_depth_1388_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_levelAssignDepth_1389_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_lmvarCounter_1390_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_mvarCounter_1391_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_lDecls_1392_);
lean_ctor_set(v_reuseFailAlloc_1410_, 5, v_decls_1393_);
lean_ctor_set(v_reuseFailAlloc_1410_, 6, v_userNames_1394_);
lean_ctor_set(v_reuseFailAlloc_1410_, 7, v_lAssignment_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 8, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 9, v_dAssignment_1397_);
v___x_1403_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1403_);
v___x_1405_ = v___x_1386_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_cache_1381_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_zetaDeltaFVarIds_1382_);
lean_ctor_set(v_reuseFailAlloc_1409_, 3, v_postponed_1383_);
lean_ctor_set(v_reuseFailAlloc_1409_, 4, v_diag_1384_);
v___x_1405_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_st_ref_set(v___y_1377_, v___x_1405_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1413_, lean_object* v_val_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1413_, v_val_1414_, v___y_1415_);
lean_dec(v___y_1415_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
lean_inc(v_g_1418_);
v___x_1424_ = l_Lean_MVarId_getType(v_g_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Lean_Meta_synthInstance(v_a_1425_, v___x_1426_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1429_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1418_, v_a_1428_, v___y_1420_);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v___x_1429_, 0);
lean_dec(v_unused_1438_);
v___x_1431_ = v___x_1429_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_dec(v___x_1429_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_box(0);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_g_1418_);
v_a_1439_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1427_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1427_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_g_1418_);
v_a_1447_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1424_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1424_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
v___f_1464_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1465_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1463_, v___f_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1466_, lean_object* v_val_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1466_, v_val_1467_, v___y_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1474_, lean_object* v_val_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1474_, v_val_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1483_, v_x_1484_, v_x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1487_, lean_object* v_x_1488_, size_t v_x_1489_, size_t v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1488_, v_x_1489_, v_x_1490_, v_x_1491_, v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_){
_start:
{
size_t v_x_1149__boxed_1500_; size_t v_x_1150__boxed_1501_; lean_object* v_res_1502_; 
v_x_1149__boxed_1500_ = lean_unbox_usize(v_x_1496_);
lean_dec(v_x_1496_);
v_x_1150__boxed_1501_ = lean_unbox_usize(v_x_1497_);
lean_dec(v_x_1497_);
v_res_1502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1494_, v_x_1495_, v_x_1149__boxed_1500_, v_x_1150__boxed_1501_, v_x_1498_, v_x_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1503_, lean_object* v_n_1504_, lean_object* v_k_1505_, lean_object* v_v_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1504_, v_k_1505_, v_v_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1508_, size_t v_depth_1509_, lean_object* v_keys_1510_, lean_object* v_vals_1511_, lean_object* v_heq_1512_, lean_object* v_i_1513_, lean_object* v_entries_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1509_, v_keys_1510_, v_vals_1511_, v_i_1513_, v_entries_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1516_, lean_object* v_depth_1517_, lean_object* v_keys_1518_, lean_object* v_vals_1519_, lean_object* v_heq_1520_, lean_object* v_i_1521_, lean_object* v_entries_1522_){
_start:
{
size_t v_depth_boxed_1523_; lean_object* v_res_1524_; 
v_depth_boxed_1523_ = lean_unbox_usize(v_depth_1517_);
lean_dec(v_depth_1517_);
v_res_1524_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1516_, v_depth_boxed_1523_, v_keys_1518_, v_vals_1519_, v_heq_1520_, v_i_1521_, v_entries_1522_);
lean_dec_ref(v_vals_1519_);
lean_dec_ref(v_keys_1518_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1526_, v_x_1527_, v_x_1528_, v_x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1531_, lean_object* v_discharge_1532_, lean_object* v_g_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v_g_1533_);
v___x_1539_ = lean_apply_6(v_discharge_1531_, v_g_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, lean_box(0));
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_dec(v_g_1533_);
lean_dec_ref(v_discharge_1532_);
return v___x_1539_;
}
else
{
lean_object* v_a_1540_; uint8_t v___y_1542_; uint8_t v___x_1544_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
v___x_1544_ = l_Lean_Exception_isInterrupt(v_a_1540_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Lean_Exception_isRuntime(v_a_1540_);
v___y_1542_ = v___x_1545_;
goto v___jp_1541_;
}
else
{
lean_dec(v_a_1540_);
v___y_1542_ = v___x_1544_;
goto v___jp_1541_;
}
v___jp_1541_:
{
if (v___y_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec_ref_known(v___x_1539_, 1);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1536_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
v___x_1543_ = lean_apply_6(v_discharge_1532_, v_g_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, lean_box(0));
return v___x_1543_;
}
else
{
lean_dec(v_g_1533_);
lean_dec_ref(v_discharge_1532_);
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1546_, lean_object* v_discharge_1547_, lean_object* v_g_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1546_, v_discharge_1547_, v_g_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1555_, lean_object* v_discharge_1556_){
_start:
{
lean_object* v_toApplyRulesConfig_1557_; lean_object* v_toBacktrackConfig_1558_; uint8_t v_backtracking_1559_; uint8_t v_intro_1560_; uint8_t v_constructor_1561_; uint8_t v_suggestions_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1594_; 
v_toApplyRulesConfig_1557_ = lean_ctor_get(v_cfg_1555_, 0);
lean_inc_ref(v_toApplyRulesConfig_1557_);
v_toBacktrackConfig_1558_ = lean_ctor_get(v_toApplyRulesConfig_1557_, 0);
lean_inc_ref(v_toBacktrackConfig_1558_);
v_backtracking_1559_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*1);
v_intro_1560_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*1 + 1);
v_constructor_1561_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*1 + 2);
v_suggestions_1562_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*1 + 3);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_cfg_1555_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_cfg_1555_, 0);
lean_dec(v_unused_1595_);
v___x_1564_ = v_cfg_1555_;
v_isShared_1565_ = v_isSharedCheck_1594_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v_cfg_1555_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1594_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_toApplyConfig_1566_; uint8_t v_transparency_1567_; uint8_t v_symm_1568_; uint8_t v_exfalso_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1592_; 
v_toApplyConfig_1566_ = lean_ctor_get(v_toApplyRulesConfig_1557_, 1);
v_transparency_1567_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1557_, sizeof(void*)*2);
v_symm_1568_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1557_, sizeof(void*)*2 + 1);
v_exfalso_1569_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1557_, sizeof(void*)*2 + 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_toApplyRulesConfig_1557_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_toApplyRulesConfig_1557_, 0);
lean_dec(v_unused_1593_);
v___x_1571_ = v_toApplyRulesConfig_1557_;
v_isShared_1572_ = v_isSharedCheck_1592_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_toApplyConfig_1566_);
lean_dec(v_toApplyRulesConfig_1557_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1592_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v_maxDepth_1573_; lean_object* v_proc_1574_; lean_object* v_suspend_1575_; lean_object* v_discharge_1576_; uint8_t v_commitIndependentGoals_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1591_; 
v_maxDepth_1573_ = lean_ctor_get(v_toBacktrackConfig_1558_, 0);
v_proc_1574_ = lean_ctor_get(v_toBacktrackConfig_1558_, 1);
v_suspend_1575_ = lean_ctor_get(v_toBacktrackConfig_1558_, 2);
v_discharge_1576_ = lean_ctor_get(v_toBacktrackConfig_1558_, 3);
v_commitIndependentGoals_1577_ = lean_ctor_get_uint8(v_toBacktrackConfig_1558_, sizeof(void*)*4);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_toBacktrackConfig_1558_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1579_ = v_toBacktrackConfig_1558_;
v_isShared_1580_ = v_isSharedCheck_1591_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_discharge_1576_);
lean_inc(v_suspend_1575_);
lean_inc(v_proc_1574_);
lean_inc(v_maxDepth_1573_);
lean_dec(v_toBacktrackConfig_1558_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1591_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___f_1581_; lean_object* v___x_1583_; 
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1581_, 0, v_discharge_1556_);
lean_closure_set(v___f_1581_, 1, v_discharge_1576_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 3, v___f_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_maxDepth_1573_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_proc_1574_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_suspend_1575_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v___f_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*4, v_commitIndependentGoals_1577_);
v___x_1583_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1583_);
v___x_1585_ = v___x_1571_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_toApplyConfig_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*2, v_transparency_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*2 + 1, v_symm_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1589_, sizeof(void*)*2 + 2, v_exfalso_1569_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1585_);
v___x_1587_ = v___x_1564_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*1, v_backtracking_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*1 + 1, v_intro_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*1 + 2, v_constructor_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*1 + 3, v_suggestions_1562_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = 1;
v___x_1603_ = l_Lean_Meta_intro1Core(v_g_1596_, v___x_1602_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1622_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1622_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1622_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_snd_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1620_; 
v_snd_1608_ = lean_ctor_get(v_a_1604_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_a_1604_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v_a_1604_, 0);
lean_dec(v_unused_1621_);
v___x_1610_ = v_a_1604_;
v_isShared_1611_ = v_isSharedCheck_1620_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_snd_1608_);
lean_dec(v_a_1604_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1620_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_box(0);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 1);
lean_ctor_set(v___x_1610_, 1, v___x_1612_);
lean_ctor_set(v___x_1610_, 0, v_snd_1608_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_snd_1608_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1615_);
v___x_1617_ = v___x_1606_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v_a_1623_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1603_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1603_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1639_){
_start:
{
lean_object* v___f_1640_; lean_object* v___x_1641_; 
v___f_1640_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1641_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1639_, v___f_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1653_ = l_Lean_MVarId_constructor(v_g_1646_, v___x_1652_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_a_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1653_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1653_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1679_){
_start:
{
lean_object* v___f_1680_; lean_object* v___x_1681_; 
v___f_1680_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1681_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1679_, v___f_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
lean_inc(v_g_1684_);
v___x_1690_ = l_Lean_MVarId_getType(v_g_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = lean_box(0);
v___x_1693_ = l_Lean_Meta_synthInstance(v_a_1691_, v___x_1692_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1703_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1684_, v_a_1694_, v___y_1686_);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v___x_1695_, 0);
lean_dec(v_unused_1704_);
v___x_1697_ = v___x_1695_;
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
else
{
lean_dec(v___x_1695_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1699_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_g_1684_);
v_a_1705_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1693_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1693_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_g_1684_);
v_a_1713_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1690_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1690_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1729_){
_start:
{
lean_object* v___f_1730_; lean_object* v___x_1731_; 
v___f_1730_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1731_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1729_, v___f_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Lean_Expr_hasMVar(v_e_1732_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_e_1732_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; lean_object* v_mctx_1738_; lean_object* v___x_1739_; lean_object* v_fst_1740_; lean_object* v_snd_1741_; lean_object* v___x_1742_; lean_object* v_cache_1743_; lean_object* v_zetaDeltaFVarIds_1744_; lean_object* v_postponed_1745_; lean_object* v_diag_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1755_; 
v___x_1737_ = lean_st_ref_get(v___y_1733_);
v_mctx_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_mctx_1738_);
lean_dec(v___x_1737_);
v___x_1739_ = l_Lean_instantiateMVarsCore(v_mctx_1738_, v_e_1732_);
v_fst_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_fst_1740_);
v_snd_1741_ = lean_ctor_get(v___x_1739_, 1);
lean_inc(v_snd_1741_);
lean_dec_ref(v___x_1739_);
v___x_1742_ = lean_st_ref_take(v___y_1733_);
v_cache_1743_ = lean_ctor_get(v___x_1742_, 1);
v_zetaDeltaFVarIds_1744_ = lean_ctor_get(v___x_1742_, 2);
v_postponed_1745_ = lean_ctor_get(v___x_1742_, 3);
v_diag_1746_ = lean_ctor_get(v___x_1742_, 4);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v___x_1742_, 0);
lean_dec(v_unused_1756_);
v___x_1748_ = v___x_1742_;
v_isShared_1749_ = v_isSharedCheck_1755_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_diag_1746_);
lean_inc(v_postponed_1745_);
lean_inc(v_zetaDeltaFVarIds_1744_);
lean_inc(v_cache_1743_);
lean_dec(v___x_1742_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1755_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v_snd_1741_);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_snd_1741_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_cache_1743_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_zetaDeltaFVarIds_1744_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_postponed_1745_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v_diag_1746_);
v___x_1751_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_st_ref_set(v___y_1733_, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_fst_1740_);
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1757_, v___y_1758_);
lean_dec(v___y_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1761_, v___y_1763_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1775_, lean_object* v_x_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1775_, v_x_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1782_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1782_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1799_, v_x_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1807_, lean_object* v_mvarId_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1808_, v_x_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1816_, lean_object* v_mvarId_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1816_, v_mvarId_1817_, v_x_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_ref_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1841_; 
v_ref_1831_ = lean_ctor_get(v___y_1828_, 5);
v___x_1832_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2_spec__5(v_msg_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_inc(v_ref_1831_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_ref_1831_);
lean_ctor_set(v___x_1837_, 1, v_a_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
if (lean_obj_tag(v_x_1849_) == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = l_List_reverse___redArg(v_x_1850_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
else
{
lean_object* v_head_1858_; lean_object* v_tail_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1879_; 
v_head_1858_ = lean_ctor_get(v_x_1849_, 0);
v_tail_1859_ = lean_ctor_get(v_x_1849_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_x_1849_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1861_ = v_x_1849_;
v_isShared_1862_ = v_isSharedCheck_1879_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_tail_1859_);
lean_inc(v_head_1858_);
lean_dec(v_x_1849_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1879_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_inc(v_head_1858_);
v___x_1863_ = l_Lean_Expr_mvar___override(v_head_1858_);
v___x_1864_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1864_, 0, v___x_1863_);
v___x_1865_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1858_, v___x_1864_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v_x_1850_);
lean_ctor_set(v___x_1861_, 0, v_a_1866_);
v___x_1868_ = v___x_1861_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1866_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_x_1850_);
v___x_1868_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
v_x_1849_ = v_tail_1859_;
v_x_1850_ = v___x_1868_;
goto _start;
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_del_object(v___x_1861_);
lean_dec(v_tail_1859_);
lean_dec(v_x_1850_);
v_a_1871_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1865_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1865_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_1880_, v_x_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1887_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_1890_ = l_Lean_stringToMessageData(v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_1891_, lean_object* v_proc_1892_, lean_object* v_orig_1893_, lean_object* v_goals_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_box(0);
lean_inc(v_orig_1893_);
v___x_1901_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_1893_, v___x_1900_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1903_ = lean_apply_6(v_test_1891_, v_a_1902_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, lean_box(0));
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; uint8_t v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = lean_unbox(v_a_1904_);
lean_dec(v_a_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_goals_1894_);
lean_dec(v_orig_1893_);
lean_dec_ref(v_proc_1892_);
v___x_1906_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_1907_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_1906_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v___x_1916_; 
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1916_ = lean_apply_7(v_proc_1892_, v_orig_1893_, v_goals_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, lean_box(0));
return v___x_1916_;
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_goals_1894_);
lean_dec(v_orig_1893_);
lean_dec_ref(v_proc_1892_);
v_a_1917_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1903_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1903_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_goals_1894_);
lean_dec(v_orig_1893_);
lean_dec_ref(v_proc_1892_);
lean_dec_ref(v_test_1891_);
v_a_1925_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1901_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1901_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_1933_, lean_object* v_proc_1934_, lean_object* v_orig_1935_, lean_object* v_goals_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_1933_, v_proc_1934_, v_orig_1935_, v_goals_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_1943_, lean_object* v_test_1944_){
_start:
{
lean_object* v_toApplyRulesConfig_1945_; lean_object* v_toBacktrackConfig_1946_; uint8_t v_backtracking_1947_; uint8_t v_intro_1948_; uint8_t v_constructor_1949_; uint8_t v_suggestions_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1982_; 
v_toApplyRulesConfig_1945_ = lean_ctor_get(v_cfg_1943_, 0);
lean_inc_ref(v_toApplyRulesConfig_1945_);
v_toBacktrackConfig_1946_ = lean_ctor_get(v_toApplyRulesConfig_1945_, 0);
lean_inc_ref(v_toBacktrackConfig_1946_);
v_backtracking_1947_ = lean_ctor_get_uint8(v_cfg_1943_, sizeof(void*)*1);
v_intro_1948_ = lean_ctor_get_uint8(v_cfg_1943_, sizeof(void*)*1 + 1);
v_constructor_1949_ = lean_ctor_get_uint8(v_cfg_1943_, sizeof(void*)*1 + 2);
v_suggestions_1950_ = lean_ctor_get_uint8(v_cfg_1943_, sizeof(void*)*1 + 3);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_cfg_1943_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_cfg_1943_, 0);
lean_dec(v_unused_1983_);
v___x_1952_ = v_cfg_1943_;
v_isShared_1953_ = v_isSharedCheck_1982_;
goto v_resetjp_1951_;
}
else
{
lean_dec(v_cfg_1943_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1982_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_toApplyConfig_1954_; uint8_t v_transparency_1955_; uint8_t v_symm_1956_; uint8_t v_exfalso_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1980_; 
v_toApplyConfig_1954_ = lean_ctor_get(v_toApplyRulesConfig_1945_, 1);
v_transparency_1955_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1945_, sizeof(void*)*2);
v_symm_1956_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1945_, sizeof(void*)*2 + 1);
v_exfalso_1957_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1945_, sizeof(void*)*2 + 2);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_toApplyRulesConfig_1945_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v_toApplyRulesConfig_1945_, 0);
lean_dec(v_unused_1981_);
v___x_1959_ = v_toApplyRulesConfig_1945_;
v_isShared_1960_ = v_isSharedCheck_1980_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_toApplyConfig_1954_);
lean_dec(v_toApplyRulesConfig_1945_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1980_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_maxDepth_1961_; lean_object* v_proc_1962_; lean_object* v_suspend_1963_; lean_object* v_discharge_1964_; uint8_t v_commitIndependentGoals_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1979_; 
v_maxDepth_1961_ = lean_ctor_get(v_toBacktrackConfig_1946_, 0);
v_proc_1962_ = lean_ctor_get(v_toBacktrackConfig_1946_, 1);
v_suspend_1963_ = lean_ctor_get(v_toBacktrackConfig_1946_, 2);
v_discharge_1964_ = lean_ctor_get(v_toBacktrackConfig_1946_, 3);
v_commitIndependentGoals_1965_ = lean_ctor_get_uint8(v_toBacktrackConfig_1946_, sizeof(void*)*4);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_toBacktrackConfig_1946_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1967_ = v_toBacktrackConfig_1946_;
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_discharge_1964_);
lean_inc(v_suspend_1963_);
lean_inc(v_proc_1962_);
lean_inc(v_maxDepth_1961_);
lean_dec(v_toBacktrackConfig_1946_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1979_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___f_1969_; lean_object* v___x_1971_; 
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1969_, 0, v_test_1944_);
lean_closure_set(v___f_1969_, 1, v_proc_1962_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v___f_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_maxDepth_1961_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___f_1969_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_suspend_1963_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_discharge_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*4, v_commitIndependentGoals_1965_);
v___x_1971_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1973_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1971_);
v___x_1973_ = v___x_1959_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_toApplyConfig_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*2, v_transparency_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*2 + 1, v_symm_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*2 + 2, v_exfalso_1957_);
v___x_1973_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1973_);
v___x_1975_ = v___x_1952_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*1, v_backtracking_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*1 + 1, v_intro_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*1 + 2, v_constructor_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*1 + 3, v_suggestions_1950_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_1984_, lean_object* v_msg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_1992_, lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_1992_, v_msg_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1999_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2000_){
_start:
{
if (lean_obj_tag(v_x_2000_) == 0)
{
uint8_t v___x_2001_; 
v___x_2001_ = 0;
return v___x_2001_;
}
else
{
lean_object* v_head_2002_; lean_object* v_tail_2003_; uint8_t v___x_2004_; 
v_head_2002_ = lean_ctor_get(v_x_2000_, 0);
v_tail_2003_ = lean_ctor_get(v_x_2000_, 1);
v___x_2004_ = l_Lean_Expr_hasMVar(v_head_2002_);
if (v___x_2004_ == 0)
{
v_x_2000_ = v_tail_2003_;
goto _start;
}
else
{
return v___x_2004_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2006_){
_start:
{
uint8_t v_res_2007_; lean_object* v_r_2008_; 
v_res_2007_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2006_);
lean_dec(v_x_2006_);
v_r_2008_ = lean_box(v_res_2007_);
return v_r_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2009_, lean_object* v_sols_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2010_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
v___x_2017_ = lean_apply_6(v_test_2009_, v_sols_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, lean_box(0));
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_sols_2010_);
lean_dec_ref(v_test_2009_);
v___x_2018_ = lean_box(v___x_2016_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2020_, lean_object* v_sols_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2020_, v_sols_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2028_, lean_object* v_test_2029_){
_start:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; 
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2030_, 0, v_test_2029_);
v___x_2031_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2028_, v___f_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
uint8_t v___x_2034_; 
lean_dec_ref(v_e_2032_);
v___x_2034_ = 0;
return v___x_2034_;
}
else
{
lean_object* v_head_2035_; lean_object* v_tail_2036_; uint8_t v___x_2037_; 
v_head_2035_ = lean_ctor_get(v_x_2033_, 0);
v_tail_2036_ = lean_ctor_get(v_x_2033_, 1);
lean_inc_ref(v_e_2032_);
v___x_2037_ = l_Lean_Expr_occurs(v_e_2032_, v_head_2035_);
if (v___x_2037_ == 0)
{
v_x_2033_ = v_tail_2036_;
goto _start;
}
else
{
lean_dec_ref(v_e_2032_);
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2039_, lean_object* v_x_2040_){
_start:
{
uint8_t v_res_2041_; lean_object* v_r_2042_; 
v_res_2041_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2039_, v_x_2040_);
lean_dec(v_x_2040_);
v_r_2042_ = lean_box(v_res_2041_);
return v_r_2042_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2043_, lean_object* v_x_2044_){
_start:
{
if (lean_obj_tag(v_x_2044_) == 0)
{
uint8_t v___x_2045_; 
v___x_2045_ = 1;
return v___x_2045_;
}
else
{
lean_object* v_head_2046_; lean_object* v_tail_2047_; uint8_t v___x_2048_; 
v_head_2046_ = lean_ctor_get(v_x_2044_, 0);
lean_inc(v_head_2046_);
v_tail_2047_ = lean_ctor_get(v_x_2044_, 1);
lean_inc(v_tail_2047_);
lean_dec_ref_known(v_x_2044_, 2);
v___x_2048_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2046_, v_sols_2043_);
if (v___x_2048_ == 0)
{
lean_dec(v_tail_2047_);
return v___x_2048_;
}
else
{
v_x_2044_ = v_tail_2047_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2050_, lean_object* v_x_2051_){
_start:
{
uint8_t v_res_2052_; lean_object* v_r_2053_; 
v_res_2052_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2050_, v_x_2051_);
lean_dec(v_sols_2050_);
v_r_2053_ = lean_box(v_res_2052_);
return v_r_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2054_, lean_object* v_sols_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2055_, v_use_2054_);
v___x_2062_ = lean_box(v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2064_, lean_object* v_sols_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2064_, v_sols_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v_sols_2065_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2072_, lean_object* v_use_2073_){
_start:
{
lean_object* v___f_2074_; lean_object* v___x_2075_; 
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2074_, 0, v_use_2073_);
v___x_2075_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2072_, v___f_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2076_){
_start:
{
lean_object* v___y_2078_; lean_object* v_toApplyRulesConfig_2079_; uint8_t v_backtracking_2080_; uint8_t v_intro_2081_; uint8_t v_constructor_2082_; uint8_t v_suggestions_2083_; uint8_t v_intro_2087_; 
v_intro_2087_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1 + 1);
if (v_intro_2087_ == 0)
{
lean_object* v_toApplyRulesConfig_2088_; uint8_t v_backtracking_2089_; uint8_t v_constructor_2090_; uint8_t v_suggestions_2091_; 
v_toApplyRulesConfig_2088_ = lean_ctor_get(v_cfg_2076_, 0);
lean_inc_ref(v_toApplyRulesConfig_2088_);
v_backtracking_2089_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1);
v_constructor_2090_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1 + 2);
v_suggestions_2091_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1 + 3);
v___y_2078_ = v_cfg_2076_;
v_toApplyRulesConfig_2079_ = v_toApplyRulesConfig_2088_;
v_backtracking_2080_ = v_backtracking_2089_;
v_intro_2081_ = v_intro_2087_;
v_constructor_2082_ = v_constructor_2090_;
v_suggestions_2083_ = v_suggestions_2091_;
goto v___jp_2077_;
}
else
{
lean_object* v_toApplyRulesConfig_2092_; uint8_t v_backtracking_2093_; uint8_t v_constructor_2094_; uint8_t v_suggestions_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2109_; 
v_toApplyRulesConfig_2092_ = lean_ctor_get(v_cfg_2076_, 0);
v_backtracking_2093_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1);
v_constructor_2094_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1 + 2);
v_suggestions_2095_ = lean_ctor_get_uint8(v_cfg_2076_, sizeof(void*)*1 + 3);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_cfg_2076_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2097_ = v_cfg_2076_;
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_toApplyRulesConfig_2092_);
lean_dec(v_cfg_2076_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
uint8_t v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = 0;
if (v_isShared_2098_ == 0)
{
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_toApplyRulesConfig_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*1, v_backtracking_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*1 + 2, v_constructor_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*1 + 3, v_suggestions_2095_);
v___x_2101_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v_toApplyRulesConfig_2103_; uint8_t v_backtracking_2104_; uint8_t v_intro_2105_; uint8_t v_constructor_2106_; uint8_t v_suggestions_2107_; 
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*1 + 1, v___x_2099_);
v___x_2102_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2101_);
v_toApplyRulesConfig_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc_ref(v_toApplyRulesConfig_2103_);
v_backtracking_2104_ = lean_ctor_get_uint8(v___x_2102_, sizeof(void*)*1);
v_intro_2105_ = lean_ctor_get_uint8(v___x_2102_, sizeof(void*)*1 + 1);
v_constructor_2106_ = lean_ctor_get_uint8(v___x_2102_, sizeof(void*)*1 + 2);
v_suggestions_2107_ = lean_ctor_get_uint8(v___x_2102_, sizeof(void*)*1 + 3);
v___y_2078_ = v___x_2102_;
v_toApplyRulesConfig_2079_ = v_toApplyRulesConfig_2103_;
v_backtracking_2080_ = v_backtracking_2104_;
v_intro_2081_ = v_intro_2105_;
v_constructor_2082_ = v_constructor_2106_;
v_suggestions_2083_ = v_suggestions_2107_;
goto v___jp_2077_;
}
}
}
v___jp_2077_:
{
if (v_constructor_2082_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2079_);
return v___y_2078_;
}
else
{
uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec_ref(v___y_2078_);
v___x_2084_ = 0;
v___x_2085_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2085_, 0, v_toApplyRulesConfig_2079_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*1, v_backtracking_2080_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*1 + 1, v_intro_2081_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*1 + 2, v___x_2084_);
lean_ctor_set_uint8(v___x_2085_, sizeof(void*)*1 + 3, v_suggestions_2083_);
v___x_2086_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2085_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
if (lean_obj_tag(v_x_2110_) == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = l_List_reverse___redArg(v_x_2111_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
else
{
lean_object* v_head_2121_; lean_object* v_tail_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2140_; 
v_head_2121_ = lean_ctor_get(v_x_2110_, 0);
v_tail_2122_ = lean_ctor_get(v_x_2110_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_x_2110_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2124_ = v_x_2110_;
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_tail_2122_);
lean_inc(v_head_2121_);
lean_dec(v_x_2110_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; 
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
v___x_2126_ = lean_apply_7(v_head_2121_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, lean_box(0));
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_x_2111_);
lean_ctor_set(v___x_2124_, 0, v_a_2127_);
v___x_2129_ = v___x_2124_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2127_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_x_2111_);
v___x_2129_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
v_x_2110_ = v_tail_2122_;
v_x_2111_ = v___x_2129_;
goto _start;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2124_);
lean_dec(v_tail_2122_);
lean_dec(v_x_2111_);
v_a_2132_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2126_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2126_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2141_, lean_object* v_x_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2141_, v_x_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2151_, lean_object* v_cfg_2152_, lean_object* v_lemmas_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; 
lean_inc(v___y_2159_);
lean_inc_ref(v___y_2158_);
lean_inc(v___y_2157_);
lean_inc_ref(v___y_2156_);
lean_inc(v___y_2155_);
lean_inc_ref(v___y_2154_);
v___x_2161_ = lean_apply_8(v_ctx_2151_, v_cfg_2152_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, lean_box(0));
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = lean_box(0);
v___x_2164_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2153_, v___x_2163_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = l_List_appendTR___redArg(v_a_2162_, v_a_2165_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_dec(v_a_2162_);
return v___x_2164_;
}
}
else
{
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v_lemmas_2153_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2174_, lean_object* v_cfg_2175_, lean_object* v_lemmas_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2174_, v_cfg_2175_, v_lemmas_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v_res_2184_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2185_){
_start:
{
uint8_t v___x_2186_; 
v___x_2186_ = 0;
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2187_){
_start:
{
uint8_t v_res_2188_; lean_object* v_r_2189_; 
v_res_2188_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2187_);
lean_dec(v_x_2187_);
v_r_2189_ = lean_box(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2190_, lean_object* v___x_2191_, lean_object* v___x_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2190_, v___x_2191_, v___x_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2207_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_fst_2203_; lean_object* v___x_2205_; 
v_fst_2203_ = lean_ctor_get(v_a_2199_, 0);
lean_inc(v_fst_2203_);
lean_dec(v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v_fst_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_fst_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2208_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2198_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2198_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2216_, lean_object* v___x_2217_, lean_object* v___x_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2216_, v___x_2217_, v___x_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2239_, lean_object* v_g_2240_, lean_object* v_lemmas_2241_, lean_object* v_ctx_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; 
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2248_, 0, v_ctx_2242_);
lean_closure_set(v___f_2248_, 1, v_cfg_2239_);
lean_closure_set(v___f_2248_, 2, v_lemmas_2241_);
v___x_2249_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2250_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2251_, 0, v___f_2248_);
lean_closure_set(v___f_2251_, 1, v___x_2249_);
lean_closure_set(v___f_2251_, 2, v___x_2250_);
v___x_2252_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2240_, v___f_2251_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2253_, lean_object* v_g_2254_, lean_object* v_lemmas_2255_, lean_object* v_ctx_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2253_, v_g_2254_, v_lemmas_2255_, v_ctx_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2263_, lean_object* v_lemmas_2264_, lean_object* v_ctx_2265_, lean_object* v_g_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v___x_2272_; 
lean_inc(v_g_2266_);
lean_inc_ref(v_cfg_2263_);
v___x_2272_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2263_, v_g_2266_, v_lemmas_2264_, v_ctx_2265_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_toApplyRulesConfig_2273_; lean_object* v_a_2274_; lean_object* v_toApplyConfig_2275_; uint8_t v_transparency_2276_; lean_object* v___x_2277_; 
v_toApplyRulesConfig_2273_ = lean_ctor_get(v_cfg_2263_, 0);
lean_inc_ref(v_toApplyRulesConfig_2273_);
lean_dec_ref(v_cfg_2263_);
v_a_2274_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2272_, 1);
v_toApplyConfig_2275_ = lean_ctor_get(v_toApplyRulesConfig_2273_, 1);
lean_inc_ref(v_toApplyConfig_2275_);
v_transparency_2276_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2273_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2273_);
v___x_2277_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2275_, v_transparency_2276_, v_a_2274_, v_g_2266_, v_a_2268_, v_a_2270_);
return v___x_2277_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_g_2266_);
lean_dec_ref(v_cfg_2263_);
v_a_2278_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2272_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2272_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2286_, lean_object* v_lemmas_2287_, lean_object* v_ctx_2288_, lean_object* v_g_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2286_, v_lemmas_2287_, v_ctx_2288_, v_g_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2296_, lean_object* v_lemmas_2297_, lean_object* v_ctx_2298_, lean_object* v_g_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v___x_2305_; 
lean_inc(v_g_2299_);
lean_inc_ref(v_cfg_2296_);
v___x_2305_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2296_, v_g_2299_, v_lemmas_2297_, v_ctx_2298_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_toApplyRulesConfig_2306_; lean_object* v_a_2307_; lean_object* v_toApplyConfig_2308_; uint8_t v_transparency_2309_; lean_object* v___x_2310_; 
v_toApplyRulesConfig_2306_ = lean_ctor_get(v_cfg_2296_, 0);
lean_inc_ref(v_toApplyRulesConfig_2306_);
lean_dec_ref(v_cfg_2296_);
v_a_2307_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2305_, 1);
v_toApplyConfig_2308_ = lean_ctor_get(v_toApplyRulesConfig_2306_, 1);
lean_inc_ref(v_toApplyConfig_2308_);
v_transparency_2309_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2306_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2306_);
v___x_2310_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2308_, v_transparency_2309_, v_a_2307_, v_g_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
return v___x_2310_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_g_2299_);
lean_dec_ref(v_cfg_2296_);
v_a_2311_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2305_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2305_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2319_, lean_object* v_lemmas_2320_, lean_object* v_ctx_2321_, lean_object* v_g_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2319_, v_lemmas_2320_, v_ctx_2321_, v_g_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
return v_res_2328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2329_, lean_object* v_i_2330_, lean_object* v_k_2331_){
_start:
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = lean_array_get_size(v_keys_2329_);
v___x_2333_ = lean_nat_dec_lt(v_i_2330_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec(v_i_2330_);
return v___x_2333_;
}
else
{
lean_object* v_k_x27_2334_; uint8_t v___x_2335_; 
v_k_x27_2334_ = lean_array_fget_borrowed(v_keys_2329_, v_i_2330_);
v___x_2335_ = l_Lean_instBEqMVarId_beq(v_k_2331_, v_k_x27_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_add(v_i_2330_, v___x_2336_);
lean_dec(v_i_2330_);
v_i_2330_ = v___x_2337_;
goto _start;
}
else
{
lean_dec(v_i_2330_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2339_, lean_object* v_i_2340_, lean_object* v_k_2341_){
_start:
{
uint8_t v_res_2342_; lean_object* v_r_2343_; 
v_res_2342_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2339_, v_i_2340_, v_k_2341_);
lean_dec(v_k_2341_);
lean_dec_ref(v_keys_2339_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2344_, size_t v_x_2345_, lean_object* v_x_2346_){
_start:
{
if (lean_obj_tag(v_x_2344_) == 0)
{
lean_object* v_es_2347_; lean_object* v___x_2348_; size_t v___x_2349_; size_t v___x_2350_; lean_object* v_j_2351_; lean_object* v___x_2352_; 
v_es_2347_ = lean_ctor_get(v_x_2344_, 0);
v___x_2348_ = lean_box(2);
v___x_2349_ = ((size_t)31ULL);
v___x_2350_ = lean_usize_land(v_x_2345_, v___x_2349_);
v_j_2351_ = lean_usize_to_nat(v___x_2350_);
v___x_2352_ = lean_array_get_borrowed(v___x_2348_, v_es_2347_, v_j_2351_);
lean_dec(v_j_2351_);
switch(lean_obj_tag(v___x_2352_))
{
case 0:
{
lean_object* v_key_2353_; uint8_t v___x_2354_; 
v_key_2353_ = lean_ctor_get(v___x_2352_, 0);
v___x_2354_ = l_Lean_instBEqMVarId_beq(v_x_2346_, v_key_2353_);
return v___x_2354_;
}
case 1:
{
lean_object* v_node_2355_; size_t v___x_2356_; size_t v___x_2357_; 
v_node_2355_ = lean_ctor_get(v___x_2352_, 0);
v___x_2356_ = ((size_t)5ULL);
v___x_2357_ = lean_usize_shift_right(v_x_2345_, v___x_2356_);
v_x_2344_ = v_node_2355_;
v_x_2345_ = v___x_2357_;
goto _start;
}
default: 
{
uint8_t v___x_2359_; 
v___x_2359_ = 0;
return v___x_2359_;
}
}
}
else
{
lean_object* v_ks_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_ks_2360_ = lean_ctor_get(v_x_2344_, 0);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2360_, v___x_2361_, v_x_2346_);
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_){
_start:
{
size_t v_x_2208__boxed_2366_; uint8_t v_res_2367_; lean_object* v_r_2368_; 
v_x_2208__boxed_2366_ = lean_unbox_usize(v_x_2364_);
lean_dec(v_x_2364_);
v_res_2367_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2363_, v_x_2208__boxed_2366_, v_x_2365_);
lean_dec(v_x_2365_);
lean_dec_ref(v_x_2363_);
v_r_2368_ = lean_box(v_res_2367_);
return v_r_2368_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
uint64_t v___x_2371_; size_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2371_ = l_Lean_instHashableMVarId_hash(v_x_2370_);
v___x_2372_ = lean_uint64_to_usize(v___x_2371_);
v___x_2373_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2369_, v___x_2372_, v_x_2370_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
uint8_t v_res_2376_; lean_object* v_r_2377_; 
v_res_2376_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2374_, v_x_2375_);
lean_dec(v_x_2375_);
lean_dec_ref(v_x_2374_);
v_r_2377_ = lean_box(v_res_2376_);
return v_r_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_mctx_2382_; lean_object* v_eAssignment_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2381_ = lean_st_ref_get(v___y_2379_);
v_mctx_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_mctx_2382_);
lean_dec(v___x_2381_);
v_eAssignment_2383_ = lean_ctor_get(v_mctx_2382_, 8);
lean_inc_ref(v_eAssignment_2383_);
lean_dec_ref(v_mctx_2382_);
v___x_2384_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2383_, v_mvarId_2378_);
lean_dec_ref(v_eAssignment_2383_);
v___x_2385_ = lean_box(v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec(v_mvarId_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
return v_x_2391_;
}
else
{
lean_object* v_head_2393_; lean_object* v_tail_2394_; lean_object* v___x_2395_; 
v_head_2393_ = lean_ctor_get(v_x_2392_, 0);
lean_inc(v_head_2393_);
v_tail_2394_ = lean_ctor_get(v_x_2392_, 1);
lean_inc(v_tail_2394_);
lean_dec_ref_known(v_x_2392_, 2);
v___x_2395_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2391_, v_head_2393_);
v_x_2391_ = v___x_2395_;
v_x_2392_ = v_tail_2394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2397_, lean_object* v_a_2398_, uint8_t v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
if (lean_obj_tag(v_a_2400_) == 0)
{
if (lean_obj_tag(v_a_2401_) == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec(v_a_2398_);
lean_dec_ref(v_f_2397_);
v___x_2408_ = lean_box(v_a_2399_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v_a_2402_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
else
{
lean_object* v_head_2411_; lean_object* v_tail_2412_; 
v_head_2411_ = lean_ctor_get(v_a_2401_, 0);
lean_inc(v_head_2411_);
v_tail_2412_ = lean_ctor_get(v_a_2401_, 1);
lean_inc(v_tail_2412_);
lean_dec_ref_known(v_a_2401_, 2);
v_a_2400_ = v_head_2411_;
v_a_2401_ = v_tail_2412_;
goto _start;
}
}
else
{
lean_object* v_head_2414_; lean_object* v_tail_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2458_; 
v_head_2414_ = lean_ctor_get(v_a_2400_, 0);
v_tail_2415_ = lean_ctor_get(v_a_2400_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_a_2400_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2417_ = v_a_2400_;
v_isShared_2418_ = v_isSharedCheck_2458_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_tail_2415_);
lean_inc(v_head_2414_);
lean_dec(v_a_2400_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2458_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2457_; 
v___x_2419_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2414_, v___y_2404_);
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2457_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2457_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_unbox(v_a_2420_);
lean_dec(v_a_2420_);
if (v___x_2424_ == 0)
{
lean_object* v_zero_2425_; uint8_t v_isZero_2426_; 
v_zero_2425_ = lean_unsigned_to_nat(0u);
v_isZero_2426_ = lean_nat_dec_eq(v_a_2398_, v_zero_2425_);
if (v_isZero_2426_ == 1)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_del_object(v___x_2417_);
lean_dec(v_a_2398_);
lean_dec_ref(v_f_2397_);
v___x_2427_ = lean_array_push(v_a_2402_, v_head_2414_);
v___x_2428_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2427_, v_tail_2415_);
v___x_2429_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2428_, v_a_2401_);
v___x_2430_ = lean_box(v_a_2399_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___x_2429_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2431_);
v___x_2433_ = v___x_2422_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_del_object(v___x_2422_);
lean_inc_ref(v_f_2397_);
lean_inc(v_head_2414_);
v___x_2435_ = lean_apply_1(v_f_2397_, v_head_2414_);
v___x_2436_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2435_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v_one_2438_; lean_object* v_n_2439_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v_one_2438_ = lean_unsigned_to_nat(1u);
v_n_2439_ = lean_nat_sub(v_a_2398_, v_one_2438_);
lean_dec(v_a_2398_);
if (lean_obj_tag(v_a_2437_) == 0)
{
lean_object* v___x_2440_; 
lean_del_object(v___x_2417_);
v___x_2440_ = lean_array_push(v_a_2402_, v_head_2414_);
v_a_2398_ = v_n_2439_;
v_a_2400_ = v_tail_2415_;
v_a_2402_ = v___x_2440_;
goto _start;
}
else
{
lean_object* v_val_2442_; uint8_t v___x_2443_; lean_object* v___x_2445_; 
lean_dec(v_head_2414_);
v_val_2442_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_val_2442_);
lean_dec_ref_known(v_a_2437_, 1);
v___x_2443_ = 1;
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 1, v_a_2401_);
lean_ctor_set(v___x_2417_, 0, v_tail_2415_);
v___x_2445_ = v___x_2417_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_tail_2415_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_a_2401_);
v___x_2445_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
v_a_2398_ = v_n_2439_;
v_a_2399_ = v___x_2443_;
v_a_2400_ = v_val_2442_;
v_a_2401_ = v___x_2445_;
goto _start;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_del_object(v___x_2417_);
lean_dec(v_tail_2415_);
lean_dec(v_head_2414_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec(v_a_2398_);
lean_dec_ref(v_f_2397_);
v_a_2448_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2436_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
else
{
lean_del_object(v___x_2422_);
lean_del_object(v___x_2417_);
lean_dec(v_head_2414_);
v_a_2400_ = v_tail_2415_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v_a_2287__boxed_2470_; lean_object* v_res_2471_; 
v_a_2287__boxed_2470_ = lean_unbox(v_a_2461_);
v_res_2471_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2459_, v_a_2460_, v_a_2287__boxed_2470_, v_a_2462_, v_a_2463_, v_a_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2472_, size_t v_i_2473_, size_t v_stop_2474_, lean_object* v_b_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_a_2482_; uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_eq(v_i_2473_, v_stop_2474_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2490_; 
v___x_2487_ = lean_array_uget_borrowed(v_as_2472_, v_i_2473_);
v___x_2490_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2487_, v___y_2477_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; uint8_t v___x_2492_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
v___x_2492_ = lean_unbox(v_a_2491_);
lean_dec(v_a_2491_);
if (v___x_2492_ == 0)
{
goto v___jp_2488_;
}
else
{
v_a_2482_ = v_b_2475_;
goto v___jp_2481_;
}
}
else
{
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2493_; uint8_t v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2490_, 1);
v___x_2494_ = lean_unbox(v_a_2493_);
lean_dec(v_a_2493_);
if (v___x_2494_ == 0)
{
v_a_2482_ = v_b_2475_;
goto v___jp_2481_;
}
else
{
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_b_2475_);
v_a_2495_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2490_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2490_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
v___jp_2488_:
{
lean_object* v___x_2489_; 
lean_inc(v___x_2487_);
v___x_2489_ = lean_array_push(v_b_2475_, v___x_2487_);
v_a_2482_ = v___x_2489_;
goto v___jp_2481_;
}
}
else
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_b_2475_);
return v___x_2503_;
}
v___jp_2481_:
{
size_t v___x_2483_; size_t v___x_2484_; 
v___x_2483_ = ((size_t)1ULL);
v___x_2484_ = lean_usize_add(v_i_2473_, v___x_2483_);
v_i_2473_ = v___x_2484_;
v_b_2475_ = v_a_2482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2504_, lean_object* v_i_2505_, lean_object* v_stop_2506_, lean_object* v_b_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
size_t v_i_boxed_2513_; size_t v_stop_boxed_2514_; lean_object* v_res_2515_; 
v_i_boxed_2513_ = lean_unbox_usize(v_i_2505_);
lean_dec(v_i_2505_);
v_stop_boxed_2514_ = lean_unbox_usize(v_stop_2506_);
lean_dec(v_stop_2506_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2504_, v_i_boxed_2513_, v_stop_boxed_2514_, v_b_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec_ref(v_as_2504_);
return v_res_2515_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2519_ = lean_array_to_list(v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2520_, lean_object* v_goals_2521_, lean_object* v_maxIters_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2528_ = 0;
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2532_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2520_, v_maxIters_2522_, v___x_2528_, v_goals_2521_, v___x_2529_, v___x_2531_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2582_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2582_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2582_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_fst_2537_; lean_object* v_snd_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2581_; 
v_fst_2537_ = lean_ctor_get(v_a_2533_, 0);
v_snd_2538_ = lean_ctor_get(v_a_2533_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_a_2533_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2540_ = v_a_2533_;
v_isShared_2541_ = v_isSharedCheck_2581_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_snd_2538_);
lean_inc(v_fst_2537_);
lean_dec(v_a_2533_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2581_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_____do__lift_2543_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2551_ = lean_array_get_size(v_snd_2538_);
v___x_2552_ = lean_nat_dec_lt(v___x_2530_, v___x_2551_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_del_object(v___x_2540_);
lean_dec(v_snd_2538_);
lean_del_object(v___x_2535_);
v___x_2553_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_fst_2537_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
else
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_nat_dec_le(v___x_2551_, v___x_2551_);
if (v___x_2556_ == 0)
{
if (v___x_2552_ == 0)
{
lean_dec(v_snd_2538_);
v_____do__lift_2543_ = v___x_2531_;
goto v___jp_2542_;
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2551_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2538_, v___x_2557_, v___x_2558_, v___x_2531_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v_snd_2538_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v_____do__lift_2543_ = v_a_2560_;
goto v___jp_2542_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_del_object(v___x_2540_);
lean_dec(v_fst_2537_);
lean_del_object(v___x_2535_);
v_a_2561_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2559_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2559_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
else
{
size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = lean_usize_of_nat(v___x_2551_);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2538_, v___x_2569_, v___x_2570_, v___x_2531_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v_snd_2538_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v_____do__lift_2543_ = v_a_2572_;
goto v___jp_2542_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_del_object(v___x_2540_);
lean_dec(v_fst_2537_);
lean_del_object(v___x_2535_);
v_a_2573_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2571_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2571_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
v___jp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = lean_array_to_list(v_____do__lift_2543_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 1, v___x_2544_);
v___x_2546_ = v___x_2540_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_fst_2537_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2546_);
v___x_2548_ = v___x_2535_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_a_2583_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2532_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2532_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2591_, lean_object* v_goals_2592_, lean_object* v_maxIters_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2591_, v_goals_2592_, v_maxIters_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2599_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2603_, lean_object* v_goals_2604_, lean_object* v_maxIters_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2603_, v_goals_2604_, v_maxIters_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2624_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2624_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2624_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v_fst_2616_; uint8_t v___x_2617_; 
v_fst_2616_ = lean_ctor_get(v_a_2612_, 0);
v___x_2617_ = lean_unbox(v_fst_2616_);
if (v___x_2617_ == 1)
{
lean_object* v_snd_2618_; lean_object* v___x_2620_; 
v_snd_2618_ = lean_ctor_get(v_a_2612_, 1);
lean_inc(v_snd_2618_);
lean_dec(v_a_2612_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_snd_2618_);
v___x_2620_ = v___x_2614_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_snd_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_del_object(v___x_2614_);
lean_dec(v_a_2612_);
v___x_2622_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2623_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2622_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
return v___x_2623_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2611_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2611_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2633_, lean_object* v_goals_2634_, lean_object* v_maxIters_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2633_, v_goals_2634_, v_maxIters_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2642_, lean_object* v_ctx_2643_, lean_object* v_cfg_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
uint8_t v_backtracking_2651_; 
v_backtracking_2651_ = lean_ctor_get_uint8(v_cfg_2644_, sizeof(void*)*1);
if (v_backtracking_2651_ == 0)
{
lean_object* v_toApplyRulesConfig_2652_; lean_object* v_toBacktrackConfig_2653_; lean_object* v_maxDepth_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_toApplyRulesConfig_2652_ = lean_ctor_get(v_cfg_2644_, 0);
v_toBacktrackConfig_2653_ = lean_ctor_get(v_toApplyRulesConfig_2652_, 0);
v_maxDepth_2654_ = lean_ctor_get(v_toBacktrackConfig_2653_, 0);
lean_inc(v_maxDepth_2654_);
v___x_2655_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2655_, 0, v_cfg_2644_);
lean_closure_set(v___x_2655_, 1, v_lemmas_2642_);
lean_closure_set(v___x_2655_, 2, v_ctx_2643_);
v___x_2656_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2655_, v_a_2645_, v_maxDepth_2654_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
return v___x_2656_;
}
else
{
lean_object* v_toApplyRulesConfig_2657_; lean_object* v_toBacktrackConfig_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_toApplyRulesConfig_2657_ = lean_ctor_get(v_cfg_2644_, 0);
v_toBacktrackConfig_2658_ = lean_ctor_get(v_toApplyRulesConfig_2657_, 0);
lean_inc_ref(v_toBacktrackConfig_2658_);
v___x_2659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2660_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2660_, 0, v_cfg_2644_);
lean_closure_set(v___x_2660_, 1, v_lemmas_2642_);
lean_closure_set(v___x_2660_, 2, v_ctx_2643_);
v___x_2661_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2658_, v___x_2659_, v___x_2660_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
return v___x_2661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2662_, lean_object* v_ctx_2663_, lean_object* v_cfg_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2662_, v_ctx_2663_, v_cfg_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2672_, v___y_2674_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v_mvarId_2679_);
return v_res_2685_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2687_, v_x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_){
_start:
{
uint8_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2690_, v_x_2691_, v_x_2692_);
lean_dec(v_x_2692_);
lean_dec_ref(v_x_2691_);
v_r_2694_ = lean_box(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2695_, lean_object* v_x_2696_, size_t v_x_2697_, lean_object* v_x_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2696_, v_x_2697_, v_x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2700_, lean_object* v_x_2701_, lean_object* v_x_2702_, lean_object* v_x_2703_){
_start:
{
size_t v_x_2747__boxed_2704_; uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_x_2747__boxed_2704_ = lean_unbox_usize(v_x_2702_);
lean_dec(v_x_2702_);
v_res_2705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2700_, v_x_2701_, v_x_2747__boxed_2704_, v_x_2703_);
lean_dec(v_x_2703_);
lean_dec_ref(v_x_2701_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2707_, lean_object* v_keys_2708_, lean_object* v_vals_2709_, lean_object* v_heq_2710_, lean_object* v_i_2711_, lean_object* v_k_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2708_, v_i_2711_, v_k_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2714_, lean_object* v_keys_2715_, lean_object* v_vals_2716_, lean_object* v_heq_2717_, lean_object* v_i_2718_, lean_object* v_k_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2714_, v_keys_2715_, v_vals_2716_, v_heq_2717_, v_i_2718_, v_k_2719_);
lean_dec(v_k_2719_);
lean_dec_ref(v_vals_2716_);
lean_dec_ref(v_keys_2715_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec_ref(v_x_2733_);
return v_res_2739_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2742_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2743_ = l_Lean_Name_append(v___x_2742_, v___x_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2744_, lean_object* v_lemmas_2745_, lean_object* v_ctx_2746_, lean_object* v_goals_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_cfg_2753_; lean_object* v___x_2754_; 
v_cfg_2753_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2744_);
lean_inc(v_goals_2747_);
lean_inc_ref(v_cfg_2753_);
lean_inc_ref(v_ctx_2746_);
lean_inc(v_lemmas_2745_);
v___x_2754_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2745_, v_ctx_2746_, v_cfg_2753_, v_goals_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_dec_ref(v_cfg_2753_);
lean_dec(v_goals_2747_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
return v___x_2754_;
}
else
{
lean_object* v_a_2755_; lean_object* v___f_2756_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; uint8_t v___y_2763_; uint8_t v___y_2764_; lean_object* v_a_2765_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; uint8_t v___y_2784_; lean_object* v_a_2785_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; uint8_t v___y_2793_; uint8_t v___y_2794_; lean_object* v_a_2795_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; uint8_t v___y_2811_; lean_object* v_a_2812_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; uint8_t v___y_2819_; lean_object* v___y_2820_; uint8_t v___y_2821_; uint8_t v___y_2857_; uint8_t v___x_2910_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
v___f_2756_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_2910_ = l_Lean_Exception_isInterrupt(v_a_2755_);
if (v___x_2910_ == 0)
{
uint8_t v___x_2911_; 
v___x_2911_ = l_Lean_Exception_isRuntime(v_a_2755_);
v___y_2857_ = v___x_2911_;
goto v___jp_2856_;
}
else
{
lean_dec(v_a_2755_);
v___y_2857_ = v___x_2910_;
goto v___jp_2856_;
}
v___jp_2757_:
{
lean_object* v___x_2766_; double v___x_2767_; double v___x_2768_; double v___x_2769_; double v___x_2770_; double v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2766_ = lean_io_mono_nanos_now();
v___x_2767_ = lean_float_of_nat(v___y_2760_);
v___x_2768_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2769_ = lean_float_div(v___x_2767_, v___x_2768_);
v___x_2770_ = lean_float_of_nat(v___x_2766_);
v___x_2771_ = lean_float_div(v___x_2770_, v___x_2768_);
v___x_2772_ = lean_box_float(v___x_2769_);
v___x_2773_ = lean_box_float(v___x_2771_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2765_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
lean_inc_ref(v___y_2758_);
lean_inc(v___y_2761_);
v___x_2776_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2761_, v___y_2764_, v___y_2758_, v___y_2759_, v___y_2763_, v___y_2762_, v___f_2756_, v___x_2775_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2776_;
}
v___jp_2777_:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v_a_2785_);
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___y_2780_;
v___y_2761_ = v___y_2781_;
v___y_2762_ = v___y_2782_;
v___y_2763_ = v___y_2783_;
v___y_2764_ = v___y_2784_;
v_a_2765_ = v___x_2786_;
goto v___jp_2757_;
}
v___jp_2787_:
{
lean_object* v___x_2796_; double v___x_2797_; double v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2796_ = lean_io_get_num_heartbeats();
v___x_2797_ = lean_float_of_nat(v___y_2788_);
v___x_2798_ = lean_float_of_nat(v___x_2796_);
v___x_2799_ = lean_box_float(v___x_2797_);
v___x_2800_ = lean_box_float(v___x_2798_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v_a_2795_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
lean_inc_ref(v___y_2789_);
lean_inc(v___y_2791_);
v___x_2803_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2791_, v___y_2794_, v___y_2789_, v___y_2790_, v___y_2793_, v___y_2792_, v___f_2756_, v___x_2802_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2803_;
}
v___jp_2804_:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v_a_2812_);
v___y_2788_ = v___y_2805_;
v___y_2789_ = v___y_2806_;
v___y_2790_ = v___y_2807_;
v___y_2791_ = v___y_2808_;
v___y_2792_ = v___y_2809_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2811_;
v_a_2795_ = v___x_2813_;
goto v___jp_2787_;
}
v___jp_2814_:
{
lean_object* v___x_2822_; lean_object* v_a_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2751_);
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2825_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2816_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_io_mono_nanos_now();
v___x_2827_ = l_Lean_MVarId_exfalso(v___y_2817_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2828_);
lean_ctor_set(v___x_2829_, 1, v___y_2820_);
v___x_2830_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2745_, v_ctx_2746_, v_cfg_2753_, v___x_2829_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 1);
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
v___y_2758_ = v___y_2815_;
v___y_2759_ = v___y_2816_;
v___y_2760_ = v___x_2826_;
v___y_2761_ = v___y_2818_;
v___y_2762_ = v_a_2823_;
v___y_2763_ = v___y_2819_;
v___y_2764_ = v___y_2821_;
v_a_2765_ = v___x_2836_;
goto v___jp_2757_;
}
}
}
else
{
lean_object* v_a_2839_; 
v_a_2839_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2830_, 1);
v___y_2778_ = v___y_2815_;
v___y_2779_ = v___y_2816_;
v___y_2780_ = v___x_2826_;
v___y_2781_ = v___y_2818_;
v___y_2782_ = v_a_2823_;
v___y_2783_ = v___y_2819_;
v___y_2784_ = v___y_2821_;
v_a_2785_ = v_a_2839_;
goto v___jp_2777_;
}
}
else
{
lean_object* v_a_2840_; 
lean_dec(v___y_2820_);
lean_dec_ref(v_cfg_2753_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
v_a_2840_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2827_, 1);
v___y_2778_ = v___y_2815_;
v___y_2779_ = v___y_2816_;
v___y_2780_ = v___x_2826_;
v___y_2781_ = v___y_2818_;
v___y_2782_ = v_a_2823_;
v___y_2783_ = v___y_2819_;
v___y_2784_ = v___y_2821_;
v_a_2785_ = v_a_2840_;
goto v___jp_2777_;
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_io_get_num_heartbeats();
v___x_2842_ = l_Lean_MVarId_exfalso(v___y_2817_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_a_2843_);
lean_ctor_set(v___x_2844_, 1, v___y_2820_);
v___x_2845_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2745_, v_ctx_2746_, v_cfg_2753_, v___x_2844_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set_tag(v___x_2848_, 1);
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
v___y_2788_ = v___x_2841_;
v___y_2789_ = v___y_2815_;
v___y_2790_ = v___y_2816_;
v___y_2791_ = v___y_2818_;
v___y_2792_ = v_a_2823_;
v___y_2793_ = v___y_2819_;
v___y_2794_ = v___y_2821_;
v_a_2795_ = v___x_2851_;
goto v___jp_2787_;
}
}
}
else
{
lean_object* v_a_2854_; 
v_a_2854_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2845_, 1);
v___y_2805_ = v___x_2841_;
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2816_;
v___y_2808_ = v___y_2818_;
v___y_2809_ = v_a_2823_;
v___y_2810_ = v___y_2819_;
v___y_2811_ = v___y_2821_;
v_a_2812_ = v_a_2854_;
goto v___jp_2804_;
}
}
else
{
lean_object* v_a_2855_; 
lean_dec(v___y_2820_);
lean_dec_ref(v_cfg_2753_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
v_a_2855_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2842_, 1);
v___y_2805_ = v___x_2841_;
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2816_;
v___y_2808_ = v___y_2818_;
v___y_2809_ = v_a_2823_;
v___y_2810_ = v___y_2819_;
v___y_2811_ = v___y_2821_;
v_a_2812_ = v_a_2855_;
goto v___jp_2804_;
}
}
}
v___jp_2856_:
{
if (v___y_2857_ == 0)
{
if (lean_obj_tag(v_goals_2747_) == 1)
{
lean_object* v_tail_2858_; 
v_tail_2858_ = lean_ctor_get(v_goals_2747_, 1);
lean_inc(v_tail_2858_);
if (lean_obj_tag(v_tail_2858_) == 0)
{
lean_object* v_toApplyRulesConfig_2859_; uint8_t v_exfalso_2860_; 
v_toApplyRulesConfig_2859_ = lean_ctor_get(v_cfg_2753_, 0);
lean_inc_ref(v_toApplyRulesConfig_2859_);
v_exfalso_2860_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2859_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2859_);
if (v_exfalso_2860_ == 1)
{
lean_object* v_options_2861_; uint8_t v_hasTrace_2862_; 
lean_dec_ref_known(v___x_2754_, 1);
v_options_2861_ = lean_ctor_get(v_a_2750_, 2);
v_hasTrace_2862_ = lean_ctor_get_uint8(v_options_2861_, sizeof(void*)*1);
if (v_hasTrace_2862_ == 0)
{
lean_object* v_head_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2881_; 
v_head_2863_ = lean_ctor_get(v_goals_2747_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_goals_2747_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v_goals_2747_, 1);
lean_dec(v_unused_2882_);
v___x_2865_ = v_goals_2747_;
v_isShared_2866_ = v_isSharedCheck_2881_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_head_2863_);
lean_dec(v_goals_2747_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2881_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_MVarId_exfalso(v_head_2863_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v_a_2868_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2868_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_tail_2858_);
v___x_2870_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2745_, v_ctx_2746_, v_cfg_2753_, v___x_2870_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2871_;
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_del_object(v___x_2865_);
lean_dec_ref(v_cfg_2753_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
v_a_2873_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2867_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2867_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v_head_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2908_; 
v_head_2883_ = lean_ctor_get(v_goals_2747_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_goals_2747_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v_goals_2747_, 1);
lean_dec(v_unused_2909_);
v___x_2885_ = v_goals_2747_;
v_isShared_2886_ = v_isSharedCheck_2908_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_head_2883_);
lean_dec(v_goals_2747_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2908_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v_inheritedTraceOptions_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_inheritedTraceOptions_2887_ = lean_ctor_get(v_a_2750_, 13);
v___x_2888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2889_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_2890_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_2891_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2887_, v_options_2861_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2892_ = l_Lean_trace_profiler;
v___x_2893_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2861_, v___x_2892_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_MVarId_exfalso(v_head_2883_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v_a_2895_);
v___x_2897_ = v___x_2885_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2895_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_tail_2858_);
v___x_2897_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2745_, v_ctx_2746_, v_cfg_2753_, v___x_2897_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2898_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_del_object(v___x_2885_);
lean_dec_ref(v_cfg_2753_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
v_a_2900_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2894_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2894_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_del_object(v___x_2885_);
v___y_2815_ = v___x_2889_;
v___y_2816_ = v_options_2861_;
v___y_2817_ = v_head_2883_;
v___y_2818_ = v___x_2888_;
v___y_2819_ = v___x_2891_;
v___y_2820_ = v_tail_2858_;
v___y_2821_ = v_exfalso_2860_;
goto v___jp_2814_;
}
}
else
{
lean_del_object(v___x_2885_);
v___y_2815_ = v___x_2889_;
v___y_2816_ = v_options_2861_;
v___y_2817_ = v_head_2883_;
v___y_2818_ = v___x_2888_;
v___y_2819_ = v___x_2891_;
v___y_2820_ = v_tail_2858_;
v___y_2821_ = v_exfalso_2860_;
goto v___jp_2814_;
}
}
}
}
else
{
lean_dec_ref_known(v_goals_2747_, 2);
lean_dec_ref(v_cfg_2753_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
return v___x_2754_;
}
}
else
{
lean_dec_ref_known(v_goals_2747_, 2);
lean_dec(v_tail_2858_);
lean_dec_ref(v_cfg_2753_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
return v___x_2754_;
}
}
else
{
lean_dec_ref(v_cfg_2753_);
lean_dec(v_goals_2747_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
return v___x_2754_;
}
}
else
{
lean_dec_ref(v_cfg_2753_);
lean_dec(v_goals_2747_);
lean_dec_ref(v_ctx_2746_);
lean_dec(v_lemmas_2745_);
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_2912_, lean_object* v_lemmas_2913_, lean_object* v_ctx_2914_, lean_object* v_goals_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_2912_, v_lemmas_2913_, v_ctx_2914_, v_goals_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = l_List_reverse___redArg(v_x_2923_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
else
{
lean_object* v_head_2931_; lean_object* v_tail_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2955_; 
v_head_2931_ = lean_ctor_get(v_x_2922_, 0);
v_tail_2932_ = lean_ctor_get(v_x_2922_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2934_ = v_x_2922_;
v_isShared_2935_ = v_isSharedCheck_2955_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_tail_2932_);
lean_inc(v_head_2931_);
lean_dec(v_x_2922_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2955_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Expr_applySymm(v_head_2931_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v_x_2923_);
lean_ctor_set(v___x_2934_, 0, v_a_2937_);
v___x_2939_ = v___x_2934_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2937_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_x_2923_);
v___x_2939_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
v_x_2922_ = v_tail_2932_;
v_x_2923_ = v___x_2939_;
goto _start;
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2954_; 
lean_del_object(v___x_2934_);
v_a_2942_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2944_ = v___x_2936_;
v_isShared_2945_ = v_isSharedCheck_2954_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2936_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2954_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
uint8_t v___y_2947_; uint8_t v___x_2952_; 
v___x_2952_ = l_Lean_Exception_isInterrupt(v_a_2942_);
if (v___x_2952_ == 0)
{
uint8_t v___x_2953_; 
lean_inc(v_a_2942_);
v___x_2953_ = l_Lean_Exception_isRuntime(v_a_2942_);
v___y_2947_ = v___x_2953_;
goto v___jp_2946_;
}
else
{
v___y_2947_ = v___x_2952_;
goto v___jp_2946_;
}
v___jp_2946_:
{
if (v___y_2947_ == 0)
{
lean_del_object(v___x_2944_);
lean_dec(v_a_2942_);
v_x_2922_ = v_tail_2932_;
goto _start;
}
else
{
lean_object* v___x_2950_; 
lean_dec(v_tail_2932_);
lean_dec(v_x_2923_);
if (v_isShared_2945_ == 0)
{
v___x_2950_ = v___x_2944_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2942_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_2956_, lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_2956_, v_x_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_2964_, lean_object* v_hyps_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
if (v_symm_2964_ == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v_hyps_2965_);
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_box(0);
lean_inc(v_hyps_2965_);
v___x_2973_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_2965_, v___x_2972_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = l_List_appendTR___redArg(v_hyps_2965_, v_a_2974_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_dec(v_hyps_2965_);
return v___x_2973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_2983_, lean_object* v_hyps_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
uint8_t v_symm_boxed_2990_; lean_object* v_res_2991_; 
v_symm_boxed_2990_ = lean_unbox(v_symm_2983_);
v_res_2991_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_2990_, v_hyps_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_2992_, size_t v_sz_2993_, size_t v_i_2994_, lean_object* v_b_2995_){
_start:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_usize_dec_lt(v_i_2994_, v_sz_2993_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2995_);
return v___x_2998_;
}
else
{
lean_object* v_snd_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3017_; 
v_snd_2999_ = lean_ctor_get(v_b_2995_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_b_2995_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v_b_2995_, 0);
lean_dec(v_unused_3018_);
v___x_3001_ = v_b_2995_;
v_isShared_3002_ = v_isSharedCheck_3017_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_snd_2999_);
lean_dec(v_b_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3017_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v_a_3005_; lean_object* v_a_3012_; 
v___x_3003_ = lean_box(0);
v_a_3012_ = lean_array_uget_borrowed(v_as_2992_, v_i_2994_);
if (lean_obj_tag(v_a_3012_) == 0)
{
v_a_3005_ = v_snd_2999_;
goto v___jp_3004_;
}
else
{
lean_object* v_val_3013_; uint8_t v___x_3014_; 
v_val_3013_ = lean_ctor_get(v_a_3012_, 0);
v___x_3014_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
lean_inc(v_val_3013_);
v___x_3015_ = l_Lean_LocalDecl_toExpr(v_val_3013_);
v___x_3016_ = lean_array_push(v_snd_2999_, v___x_3015_);
v_a_3005_ = v___x_3016_;
goto v___jp_3004_;
}
else
{
v_a_3005_ = v_snd_2999_;
goto v___jp_3004_;
}
}
v___jp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v_a_3005_);
lean_ctor_set(v___x_3001_, 0, v___x_3003_);
v___x_3007_ = v___x_3001_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_a_3005_);
v___x_3007_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
size_t v___x_3008_; size_t v___x_3009_; 
v___x_3008_ = ((size_t)1ULL);
v___x_3009_ = lean_usize_add(v_i_2994_, v___x_3008_);
v_i_2994_ = v___x_3009_;
v_b_2995_ = v___x_3007_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3019_, lean_object* v_sz_3020_, lean_object* v_i_3021_, lean_object* v_b_3022_, lean_object* v___y_3023_){
_start:
{
size_t v_sz_boxed_3024_; size_t v_i_boxed_3025_; lean_object* v_res_3026_; 
v_sz_boxed_3024_ = lean_unbox_usize(v_sz_3020_);
lean_dec(v_sz_3020_);
v_i_boxed_3025_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3019_, v_sz_boxed_3024_, v_i_boxed_3025_, v_b_3022_);
lean_dec_ref(v_as_3019_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3027_, size_t v_sz_3028_, size_t v_i_3029_, lean_object* v_b_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_usize_dec_lt(v_i_3029_, v_sz_3028_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_b_3030_);
return v___x_3039_;
}
else
{
lean_object* v_snd_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3058_; 
v_snd_3040_ = lean_ctor_get(v_b_3030_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_b_3030_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v_b_3030_, 0);
lean_dec(v_unused_3059_);
v___x_3042_ = v_b_3030_;
v_isShared_3043_ = v_isSharedCheck_3058_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_snd_3040_);
lean_dec(v_b_3030_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3058_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v_a_3046_; lean_object* v_a_3053_; 
v___x_3044_ = lean_box(0);
v_a_3053_ = lean_array_uget_borrowed(v_as_3027_, v_i_3029_);
if (lean_obj_tag(v_a_3053_) == 0)
{
v_a_3046_ = v_snd_3040_;
goto v___jp_3045_;
}
else
{
lean_object* v_val_3054_; uint8_t v___x_3055_; 
v_val_3054_ = lean_ctor_get(v_a_3053_, 0);
v___x_3055_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_inc(v_val_3054_);
v___x_3056_ = l_Lean_LocalDecl_toExpr(v_val_3054_);
v___x_3057_ = lean_array_push(v_snd_3040_, v___x_3056_);
v_a_3046_ = v___x_3057_;
goto v___jp_3045_;
}
else
{
v_a_3046_ = v_snd_3040_;
goto v___jp_3045_;
}
}
v___jp_3045_:
{
lean_object* v___x_3048_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v_a_3046_);
lean_ctor_set(v___x_3042_, 0, v___x_3044_);
v___x_3048_ = v___x_3042_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_a_3046_);
v___x_3048_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
size_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = ((size_t)1ULL);
v___x_3050_ = lean_usize_add(v_i_3029_, v___x_3049_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3027_, v_sz_3028_, v___x_3050_, v___x_3048_);
return v___x_3051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3060_, lean_object* v_sz_3061_, lean_object* v_i_3062_, lean_object* v_b_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
size_t v_sz_boxed_3071_; size_t v_i_boxed_3072_; lean_object* v_res_3073_; 
v_sz_boxed_3071_ = lean_unbox_usize(v_sz_3061_);
lean_dec(v_sz_3061_);
v_i_boxed_3072_ = lean_unbox_usize(v_i_3062_);
lean_dec(v_i_3062_);
v_res_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3060_, v_sz_boxed_3071_, v_i_boxed_3072_, v_b_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec_ref(v_as_3060_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3074_, size_t v_sz_3075_, size_t v_i_3076_, lean_object* v_b_3077_){
_start:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_usize_dec_lt(v_i_3076_, v_sz_3075_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_b_3077_);
return v___x_3080_;
}
else
{
lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3099_; 
v_snd_3081_ = lean_ctor_get(v_b_3077_, 1);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_b_3077_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v_b_3077_, 0);
lean_dec(v_unused_3100_);
v___x_3083_ = v_b_3077_;
v_isShared_3084_ = v_isSharedCheck_3099_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_dec(v_b_3077_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3099_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v_a_3087_; lean_object* v_a_3094_; 
v___x_3085_ = lean_box(0);
v_a_3094_ = lean_array_uget_borrowed(v_as_3074_, v_i_3076_);
if (lean_obj_tag(v_a_3094_) == 0)
{
v_a_3087_ = v_snd_3081_;
goto v___jp_3086_;
}
else
{
lean_object* v_val_3095_; uint8_t v___x_3096_; 
v_val_3095_ = lean_ctor_get(v_a_3094_, 0);
v___x_3096_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
lean_inc(v_val_3095_);
v___x_3097_ = l_Lean_LocalDecl_toExpr(v_val_3095_);
v___x_3098_ = lean_array_push(v_snd_3081_, v___x_3097_);
v_a_3087_ = v___x_3098_;
goto v___jp_3086_;
}
else
{
v_a_3087_ = v_snd_3081_;
goto v___jp_3086_;
}
}
v___jp_3086_:
{
lean_object* v___x_3089_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 1, v_a_3087_);
lean_ctor_set(v___x_3083_, 0, v___x_3085_);
v___x_3089_ = v___x_3083_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_a_3087_);
v___x_3089_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
size_t v___x_3090_; size_t v___x_3091_; 
v___x_3090_ = ((size_t)1ULL);
v___x_3091_ = lean_usize_add(v_i_3076_, v___x_3090_);
v_i_3076_ = v___x_3091_;
v_b_3077_ = v___x_3089_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3101_, lean_object* v_sz_3102_, lean_object* v_i_3103_, lean_object* v_b_3104_, lean_object* v___y_3105_){
_start:
{
size_t v_sz_boxed_3106_; size_t v_i_boxed_3107_; lean_object* v_res_3108_; 
v_sz_boxed_3106_ = lean_unbox_usize(v_sz_3102_);
lean_dec(v_sz_3102_);
v_i_boxed_3107_ = lean_unbox_usize(v_i_3103_);
lean_dec(v_i_3103_);
v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3101_, v_sz_boxed_3106_, v_i_boxed_3107_, v_b_3104_);
lean_dec_ref(v_as_3101_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3109_, size_t v_sz_3110_, size_t v_i_3111_, lean_object* v_b_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
uint8_t v___x_3120_; 
v___x_3120_ = lean_usize_dec_lt(v_i_3111_, v_sz_3110_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_b_3112_);
return v___x_3121_;
}
else
{
lean_object* v_snd_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3140_; 
v_snd_3122_ = lean_ctor_get(v_b_3112_, 1);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_b_3112_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v_b_3112_, 0);
lean_dec(v_unused_3141_);
v___x_3124_ = v_b_3112_;
v_isShared_3125_ = v_isSharedCheck_3140_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_snd_3122_);
lean_dec(v_b_3112_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3140_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v_a_3128_; lean_object* v_a_3135_; 
v___x_3126_ = lean_box(0);
v_a_3135_ = lean_array_uget_borrowed(v_as_3109_, v_i_3111_);
if (lean_obj_tag(v_a_3135_) == 0)
{
v_a_3128_ = v_snd_3122_;
goto v___jp_3127_;
}
else
{
lean_object* v_val_3136_; uint8_t v___x_3137_; 
v_val_3136_ = lean_ctor_get(v_a_3135_, 0);
v___x_3137_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_inc(v_val_3136_);
v___x_3138_ = l_Lean_LocalDecl_toExpr(v_val_3136_);
v___x_3139_ = lean_array_push(v_snd_3122_, v___x_3138_);
v_a_3128_ = v___x_3139_;
goto v___jp_3127_;
}
else
{
v_a_3128_ = v_snd_3122_;
goto v___jp_3127_;
}
}
v___jp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 1, v_a_3128_);
lean_ctor_set(v___x_3124_, 0, v___x_3126_);
v___x_3130_ = v___x_3124_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_a_3128_);
v___x_3130_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
size_t v___x_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = ((size_t)1ULL);
v___x_3132_ = lean_usize_add(v_i_3111_, v___x_3131_);
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3109_, v_sz_3110_, v___x_3132_, v___x_3130_);
return v___x_3133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3142_, lean_object* v_sz_3143_, lean_object* v_i_3144_, lean_object* v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
size_t v_sz_boxed_3153_; size_t v_i_boxed_3154_; lean_object* v_res_3155_; 
v_sz_boxed_3153_ = lean_unbox_usize(v_sz_3143_);
lean_dec(v_sz_3143_);
v_i_boxed_3154_ = lean_unbox_usize(v_i_3144_);
lean_dec(v_i_3144_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3142_, v_sz_boxed_3153_, v_i_boxed_3154_, v_b_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_as_3142_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3156_, lean_object* v_n_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
if (lean_obj_tag(v_n_3157_) == 0)
{
lean_object* v_cs_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; size_t v_sz_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v_cs_3166_ = lean_ctor_get(v_n_3157_, 0);
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v_b_3158_);
v_sz_3169_ = lean_array_size(v_cs_3166_);
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3156_, v_cs_3166_, v_sz_3169_, v___x_3170_, v___x_3168_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3186_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3186_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3186_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_fst_3176_; 
v_fst_3176_ = lean_ctor_get(v_a_3172_, 0);
if (lean_obj_tag(v_fst_3176_) == 0)
{
lean_object* v_snd_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v_snd_3177_ = lean_ctor_get(v_a_3172_, 1);
lean_inc(v_snd_3177_);
lean_dec(v_a_3172_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_snd_3177_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3178_);
v___x_3180_ = v___x_3174_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
lean_object* v_val_3182_; lean_object* v___x_3184_; 
lean_inc_ref(v_fst_3176_);
lean_dec(v_a_3172_);
v_val_3182_ = lean_ctor_get(v_fst_3176_, 0);
lean_inc(v_val_3182_);
lean_dec_ref_known(v_fst_3176_, 1);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v_val_3182_);
v___x_3184_ = v___x_3174_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_val_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
v_a_3187_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3171_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3171_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v_vs_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; size_t v_sz_3198_; size_t v___x_3199_; lean_object* v___x_3200_; 
v_vs_3195_ = lean_ctor_get(v_n_3157_, 0);
v___x_3196_ = lean_box(0);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v_b_3158_);
v_sz_3198_ = lean_array_size(v_vs_3195_);
v___x_3199_ = ((size_t)0ULL);
v___x_3200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3195_, v_sz_3198_, v___x_3199_, v___x_3197_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3215_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3215_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3215_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_fst_3205_; 
v_fst_3205_ = lean_ctor_get(v_a_3201_, 0);
if (lean_obj_tag(v_fst_3205_) == 0)
{
lean_object* v_snd_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v_snd_3206_ = lean_ctor_get(v_a_3201_, 1);
lean_inc(v_snd_3206_);
lean_dec(v_a_3201_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_snd_3206_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3207_);
v___x_3209_ = v___x_3203_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
else
{
lean_object* v_val_3211_; lean_object* v___x_3213_; 
lean_inc_ref(v_fst_3205_);
lean_dec(v_a_3201_);
v_val_3211_ = lean_ctor_get(v_fst_3205_, 0);
lean_inc(v_val_3211_);
lean_dec_ref_known(v_fst_3205_, 1);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v_val_3211_);
v___x_3213_ = v___x_3203_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_val_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
v_a_3216_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3200_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3200_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3224_, lean_object* v_as_3225_, size_t v_sz_3226_, size_t v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
uint8_t v___x_3236_; 
v___x_3236_ = lean_usize_dec_lt(v_i_3227_, v_sz_3226_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_b_3228_);
return v___x_3237_;
}
else
{
lean_object* v_snd_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3272_; 
v_snd_3238_ = lean_ctor_get(v_b_3228_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_b_3228_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v_b_3228_, 0);
lean_dec(v_unused_3273_);
v___x_3240_ = v_b_3228_;
v_isShared_3241_ = v_isSharedCheck_3272_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snd_3238_);
lean_dec(v_b_3228_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3272_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v_a_3242_; lean_object* v___x_3243_; 
v_a_3242_ = lean_array_uget_borrowed(v_as_3225_, v_i_3227_);
lean_inc(v_snd_3238_);
v___x_3243_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3224_, v_a_3242_, v_snd_3238_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3263_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3263_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3263_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
if (lean_obj_tag(v_a_3244_) == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_a_3244_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3248_);
v___x_3250_ = v___x_3240_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_snd_3238_);
v___x_3250_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3252_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3250_);
v___x_3252_ = v___x_3246_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
lean_del_object(v___x_3246_);
lean_dec(v_snd_3238_);
v_a_3255_ = lean_ctor_get(v_a_3244_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v_a_3244_, 1);
v___x_3256_ = lean_box(0);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v_a_3255_);
lean_ctor_set(v___x_3240_, 0, v___x_3256_);
v___x_3258_ = v___x_3240_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_a_3255_);
v___x_3258_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
size_t v___x_3259_; size_t v___x_3260_; 
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3227_, v___x_3259_);
v_i_3227_ = v___x_3260_;
v_b_3228_ = v___x_3258_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_del_object(v___x_3240_);
lean_dec(v_snd_3238_);
v_a_3264_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3243_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3243_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3274_, lean_object* v_as_3275_, lean_object* v_sz_3276_, lean_object* v_i_3277_, lean_object* v_b_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
size_t v_sz_boxed_3286_; size_t v_i_boxed_3287_; lean_object* v_res_3288_; 
v_sz_boxed_3286_ = lean_unbox_usize(v_sz_3276_);
lean_dec(v_sz_3276_);
v_i_boxed_3287_ = lean_unbox_usize(v_i_3277_);
lean_dec(v_i_3277_);
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3274_, v_as_3275_, v_sz_boxed_3286_, v_i_boxed_3287_, v_b_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec_ref(v_as_3275_);
lean_dec_ref(v_init_3274_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3289_, lean_object* v_n_3290_, lean_object* v_b_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3289_, v_n_3290_, v_b_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec_ref(v_n_3290_);
lean_dec_ref(v_init_3289_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3300_, lean_object* v_init_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_root_3309_; lean_object* v_tail_3310_; lean_object* v___x_3311_; 
v_root_3309_ = lean_ctor_get(v_t_3300_, 0);
v_tail_3310_ = lean_ctor_get(v_t_3300_, 1);
lean_inc_ref(v_init_3301_);
v___x_3311_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3301_, v_root_3309_, v_init_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec_ref(v_init_3301_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3348_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3348_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3348_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
if (lean_obj_tag(v_a_3312_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; 
v_a_3316_ = lean_ctor_get(v_a_3312_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v_a_3312_, 1);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v_a_3316_);
v___x_3318_ = v___x_3314_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; size_t v_sz_3323_; size_t v___x_3324_; lean_object* v___x_3325_; 
lean_del_object(v___x_3314_);
v_a_3320_ = lean_ctor_get(v_a_3312_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v_a_3312_, 1);
v___x_3321_ = lean_box(0);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v_a_3320_);
v_sz_3323_ = lean_array_size(v_tail_3310_);
v___x_3324_ = ((size_t)0ULL);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3310_, v_sz_3323_, v___x_3324_, v___x_3322_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3339_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3339_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3339_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_fst_3330_; 
v_fst_3330_ = lean_ctor_get(v_a_3326_, 0);
if (lean_obj_tag(v_fst_3330_) == 0)
{
lean_object* v_snd_3331_; lean_object* v___x_3333_; 
v_snd_3331_ = lean_ctor_get(v_a_3326_, 1);
lean_inc(v_snd_3331_);
lean_dec(v_a_3326_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v_snd_3331_);
v___x_3333_ = v___x_3328_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_snd_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
else
{
lean_object* v_val_3335_; lean_object* v___x_3337_; 
lean_inc_ref(v_fst_3330_);
lean_dec(v_a_3326_);
v_val_3335_ = lean_ctor_get(v_fst_3330_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v_fst_3330_, 1);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v_val_3335_);
v___x_3337_ = v___x_3328_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_val_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_a_3340_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3325_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3325_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3311_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3311_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3357_, lean_object* v_init_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3357_, v_init_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec_ref(v_t_3357_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_lctx_3376_; lean_object* v_decls_3377_; lean_object* v_hs_3378_; lean_object* v___x_3379_; 
v_lctx_3376_ = lean_ctor_get(v___y_3371_, 2);
v_decls_3377_ = lean_ctor_get(v_lctx_3376_, 1);
v_hs_3378_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3379_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3377_, v_hs_3378_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3388_, lean_object* v_cfg_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
if (v_only_3388_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_toApplyRulesConfig_3398_; lean_object* v_a_3399_; uint8_t v_symm_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_toApplyRulesConfig_3398_ = lean_ctor_get(v_cfg_3389_, 0);
v_a_3399_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3397_, 1);
v_symm_3400_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3398_, sizeof(void*)*2 + 1);
v___x_3401_ = lean_array_to_list(v_a_3399_);
v___x_3402_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3400_, v___x_3401_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
return v___x_3402_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3397_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3397_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_box(0);
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3413_, lean_object* v_cfg_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
uint8_t v_only_boxed_3422_; lean_object* v_res_3423_; 
v_only_boxed_3422_ = lean_unbox(v_only_3413_);
v_res_3423_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3422_, v_cfg_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v_cfg_3414_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3424_, lean_object* v_lemmas_3425_, uint8_t v_only_3426_, lean_object* v_g_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_toApplyRulesConfig_3433_; uint8_t v_intro_3434_; uint8_t v_constructor_3435_; uint8_t v_suggestions_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3449_; 
v_toApplyRulesConfig_3433_ = lean_ctor_get(v_cfg_3424_, 0);
v_intro_3434_ = lean_ctor_get_uint8(v_cfg_3424_, sizeof(void*)*1 + 1);
v_constructor_3435_ = lean_ctor_get_uint8(v_cfg_3424_, sizeof(void*)*1 + 2);
v_suggestions_3436_ = lean_ctor_get_uint8(v_cfg_3424_, sizeof(void*)*1 + 3);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_cfg_3424_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3438_ = v_cfg_3424_;
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_toApplyRulesConfig_3433_);
lean_dec(v_cfg_3424_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v_ctx_3441_; uint8_t v___x_3442_; lean_object* v___x_3444_; 
v___x_3440_ = lean_box(v_only_3426_);
v_ctx_3441_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3441_, 0, v___x_3440_);
v___x_3442_ = 0;
if (v_isShared_3439_ == 0)
{
v___x_3444_ = v___x_3438_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_toApplyRulesConfig_3433_);
lean_ctor_set_uint8(v_reuseFailAlloc_3448_, sizeof(void*)*1 + 1, v_intro_3434_);
lean_ctor_set_uint8(v_reuseFailAlloc_3448_, sizeof(void*)*1 + 2, v_constructor_3435_);
lean_ctor_set_uint8(v_reuseFailAlloc_3448_, sizeof(void*)*1 + 3, v_suggestions_3436_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*1, v___x_3442_);
v___x_3445_ = lean_box(0);
v___x_3446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_g_3427_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3444_, v_lemmas_3425_, v_ctx_3441_, v___x_3446_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
return v___x_3447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3450_, lean_object* v_lemmas_3451_, lean_object* v_only_3452_, lean_object* v_g_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
uint8_t v_only_boxed_3459_; lean_object* v_res_3460_; 
v_only_boxed_3459_ = lean_unbox(v_only_3452_);
v_res_3460_ = l_Lean_MVarId_applyRules(v_cfg_3450_, v_lemmas_3451_, v_only_boxed_3459_, v_g_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3461_, size_t v_sz_3462_, size_t v_i_3463_, lean_object* v_b_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3461_, v_sz_3462_, v_i_3463_, v_b_3464_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3473_, lean_object* v_sz_3474_, lean_object* v_i_3475_, lean_object* v_b_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
size_t v_sz_boxed_3484_; size_t v_i_boxed_3485_; lean_object* v_res_3486_; 
v_sz_boxed_3484_ = lean_unbox_usize(v_sz_3474_);
lean_dec(v_sz_3474_);
v_i_boxed_3485_ = lean_unbox_usize(v_i_3475_);
lean_dec(v_i_3475_);
v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3473_, v_sz_boxed_3484_, v_i_boxed_3485_, v_b_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec_ref(v_as_3473_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3487_, size_t v_sz_3488_, size_t v_i_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3487_, v_sz_3488_, v_i_3489_, v_b_3490_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3499_, lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
size_t v_sz_boxed_3510_; size_t v_i_boxed_3511_; lean_object* v_res_3512_; 
v_sz_boxed_3510_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3511_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3499_, v_sz_boxed_3510_, v_i_boxed_3511_, v_b_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_as_3499_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v___x_3521_; uint8_t v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = lean_box(0);
v___x_3522_ = 1;
v___x_3523_ = l_Lean_Elab_Term_elabTerm(v_t_3513_, v___x_3521_, v___x_3522_, v___x_3522_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_ref_3538_; uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_ref_3538_ = lean_ctor_get(v___y_3535_, 5);
v___x_3539_ = 0;
v___x_3540_ = l_Lean_SourceInfo_fromRef(v_ref_3538_, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
return v_res_3547_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3548_, lean_object* v_x_3549_){
_start:
{
if (lean_obj_tag(v_x_3549_) == 0)
{
uint8_t v___x_3550_; 
v___x_3550_ = 0;
return v___x_3550_;
}
else
{
lean_object* v_head_3551_; lean_object* v_tail_3552_; uint8_t v___x_3553_; 
v_head_3551_ = lean_ctor_get(v_x_3549_, 0);
v_tail_3552_ = lean_ctor_get(v_x_3549_, 1);
v___x_3553_ = lean_expr_eqv(v_a_3548_, v_head_3551_);
if (v___x_3553_ == 0)
{
v_x_3549_ = v_tail_3552_;
goto _start;
}
else
{
return v___x_3553_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3555_, lean_object* v_x_3556_){
_start:
{
uint8_t v_res_3557_; lean_object* v_r_3558_; 
v_res_3557_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3555_, v_x_3556_);
lean_dec(v_x_3556_);
lean_dec_ref(v_a_3555_);
v_r_3558_ = lean_box(v_res_3557_);
return v_r_3558_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3559_, lean_object* v_x_3560_){
_start:
{
uint8_t v___x_3561_; 
v___x_3561_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3560_, v_ys_3559_);
if (v___x_3561_ == 0)
{
uint8_t v___x_3562_; 
v___x_3562_ = 1;
return v___x_3562_;
}
else
{
uint8_t v___x_3563_; 
v___x_3563_ = 0;
return v___x_3563_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3564_, lean_object* v_x_3565_){
_start:
{
uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_res_3566_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3564_, v_x_3565_);
lean_dec_ref(v_x_3565_);
lean_dec(v_ys_3564_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3568_, lean_object* v_ys_3569_){
_start:
{
lean_object* v___f_3570_; lean_object* v___x_3571_; 
v___f_3570_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3570_, 0, v_ys_3569_);
v___x_3571_ = l_List_filter___redArg(v___f_3570_, v_xs_3568_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
if (lean_obj_tag(v_x_3572_) == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = l_List_reverse___redArg(v_x_3573_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
else
{
lean_object* v_head_3583_; lean_object* v_tail_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3602_; 
v_head_3583_ = lean_ctor_get(v_x_3572_, 0);
v_tail_3584_ = lean_ctor_get(v_x_3572_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3586_ = v_x_3572_;
v_isShared_3587_ = v_isSharedCheck_3602_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_tail_3584_);
lean_inc(v_head_3583_);
lean_dec(v_x_3572_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3602_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; 
v___x_3588_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3583_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v_x_3573_);
lean_ctor_set(v___x_3586_, 0, v_a_3589_);
v___x_3591_ = v___x_3586_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_x_3573_);
v___x_3591_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
v_x_3572_ = v_tail_3584_;
v_x_3573_ = v___x_3591_;
goto _start;
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_del_object(v___x_3586_);
lean_dec(v_tail_3584_);
lean_dec(v_x_3573_);
v_a_3594_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3588_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3588_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3603_, lean_object* v_x_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3603_, v_x_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3613_, uint8_t v_noDefaults_3614_, uint8_t v_star_3615_, lean_object* v_cfg_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
if (v_noDefaults_3614_ == 0)
{
goto v___jp_3624_;
}
else
{
if (v_star_3615_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec(v_remove_3613_);
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
else
{
goto v___jp_3624_;
}
}
v___jp_3624_:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v___x_3627_ = lean_box(0);
v___x_3628_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3613_, v___x_3627_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_toApplyRulesConfig_3629_; lean_object* v_a_3630_; uint8_t v_symm_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_toApplyRulesConfig_3629_ = lean_ctor_get(v_cfg_3616_, 0);
v_a_3630_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3628_, 1);
v_symm_3631_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3629_, sizeof(void*)*2 + 1);
v___x_3632_ = lean_array_to_list(v_a_3626_);
v___x_3633_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3632_, v_a_3630_);
v___x_3634_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3631_, v___x_3633_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3634_;
}
else
{
lean_dec(v_a_3626_);
return v___x_3628_;
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec(v_remove_3613_);
v_a_3635_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3625_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3625_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3645_, lean_object* v_noDefaults_3646_, lean_object* v_star_3647_, lean_object* v_cfg_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_noDefaults_boxed_3656_; uint8_t v_star_boxed_3657_; lean_object* v_res_3658_; 
v_noDefaults_boxed_3656_ = lean_unbox(v_noDefaults_3646_);
v_star_boxed_3657_ = lean_unbox(v_star_3647_);
v_res_3658_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3645_, v_noDefaults_boxed_3656_, v_star_boxed_3657_, v_cfg_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec_ref(v_cfg_3648_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3659_, size_t v_i_3660_, size_t v_stop_3661_, lean_object* v_b_3662_){
_start:
{
uint8_t v___x_3663_; 
v___x_3663_ = lean_usize_dec_eq(v_i_3660_, v_stop_3661_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3665_; size_t v___x_3666_; size_t v___x_3667_; 
v___x_3664_ = lean_array_uget_borrowed(v_as_3659_, v_i_3660_);
v___x_3665_ = l_Array_append___redArg(v_b_3662_, v___x_3664_);
v___x_3666_ = ((size_t)1ULL);
v___x_3667_ = lean_usize_add(v_i_3660_, v___x_3666_);
v_i_3660_ = v___x_3667_;
v_b_3662_ = v___x_3665_;
goto _start;
}
else
{
return v_b_3662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3669_, lean_object* v_i_3670_, lean_object* v_stop_3671_, lean_object* v_b_3672_){
_start:
{
size_t v_i_boxed_3673_; size_t v_stop_boxed_3674_; lean_object* v_res_3675_; 
v_i_boxed_3673_ = lean_unbox_usize(v_i_3670_);
lean_dec(v_i_3670_);
v_stop_boxed_3674_ = lean_unbox_usize(v_stop_3671_);
lean_dec(v_stop_3671_);
v_res_3675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3669_, v_i_boxed_3673_, v_stop_boxed_3674_, v_b_3672_);
lean_dec_ref(v_as_3669_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
if (lean_obj_tag(v_a_3676_) == 0)
{
lean_object* v___x_3678_; 
v___x_3678_ = l_List_reverse___redArg(v_a_3677_);
return v___x_3678_;
}
else
{
lean_object* v_head_3679_; lean_object* v_tail_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3689_; 
v_head_3679_ = lean_ctor_get(v_a_3676_, 0);
v_tail_3680_ = lean_ctor_get(v_a_3676_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3676_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3682_ = v_a_3676_;
v_isShared_3683_ = v_isSharedCheck_3689_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_tail_3680_);
lean_inc(v_head_3679_);
lean_dec(v_a_3676_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3689_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3684_, 0, v_head_3679_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 1, v_a_3677_);
lean_ctor_set(v___x_3682_, 0, v___x_3684_);
v___x_3686_ = v___x_3682_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_a_3677_);
v___x_3686_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
v_a_3676_ = v_tail_3680_;
v_a_3677_ = v___x_3686_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3690_, size_t v_i_3691_, lean_object* v_bs_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
uint8_t v___x_3696_; 
v___x_3696_ = lean_usize_dec_lt(v_i_3691_, v_sz_3690_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_bs_3692_);
return v___x_3697_;
}
else
{
lean_object* v_v_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_v_3698_ = lean_array_uget_borrowed(v_bs_3692_, v_i_3691_);
v___x_3699_ = l_Lean_Syntax_getId(v_v_3698_);
v___x_3700_ = l_Lean_labelled(v___x_3699_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v_bs_x27_3703_; size_t v___x_3704_; size_t v___x_3705_; lean_object* v___x_3706_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = lean_unsigned_to_nat(0u);
v_bs_x27_3703_ = lean_array_uset(v_bs_3692_, v_i_3691_, v___x_3702_);
v___x_3704_ = ((size_t)1ULL);
v___x_3705_ = lean_usize_add(v_i_3691_, v___x_3704_);
v___x_3706_ = lean_array_uset(v_bs_x27_3703_, v_i_3691_, v_a_3701_);
v_i_3691_ = v___x_3705_;
v_bs_3692_ = v___x_3706_;
goto _start;
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v_bs_3692_);
v_a_3708_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3700_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3700_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3716_, lean_object* v_i_3717_, lean_object* v_bs_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
size_t v_sz_boxed_3722_; size_t v_i_boxed_3723_; lean_object* v_res_3724_; 
v_sz_boxed_3722_ = lean_unbox_usize(v_sz_3716_);
lean_dec(v_sz_3716_);
v_i_boxed_3723_ = lean_unbox_usize(v_i_3717_);
lean_dec(v_i_3717_);
v_res_3724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3722_, v_i_boxed_3723_, v_bs_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3725_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
if (lean_obj_tag(v_a_3743_) == 0)
{
lean_object* v___x_3745_; 
v___x_3745_ = l_List_reverse___redArg(v_a_3744_);
return v___x_3745_;
}
else
{
lean_object* v_head_3746_; lean_object* v_tail_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3756_; 
v_head_3746_ = lean_ctor_get(v_a_3743_, 0);
v_tail_3747_ = lean_ctor_get(v_a_3743_, 1);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3749_ = v_a_3743_;
v_isShared_3750_ = v_isSharedCheck_3756_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_tail_3747_);
lean_inc(v_head_3746_);
lean_dec(v_a_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3756_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___f_3751_; lean_object* v___x_3753_; 
v___f_3751_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3751_, 0, v_head_3746_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v_a_3744_);
lean_ctor_set(v___x_3749_, 0, v___f_3751_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___f_3751_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_a_3744_);
v___x_3753_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
v_a_3743_ = v_tail_3747_;
v_a_3744_ = v___x_3753_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3759_ = l_Lean_stringToMessageData(v___x_3758_);
return v___x_3759_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3762_ = l_String_toRawSubstring_x27(v___x_3761_);
return v___x_3762_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3767_ = l_String_toRawSubstring_x27(v___x_3766_);
return v___x_3767_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3772_ = l_String_toRawSubstring_x27(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3777_ = l_String_toRawSubstring_x27(v___x_3776_);
return v___x_3777_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3808_ = l_Lean_stringToMessageData(v___x_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3809_, uint8_t v_star_3810_, lean_object* v_add_3811_, lean_object* v_remove_3812_, lean_object* v_use_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___f_3844_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; 
v___x_3842_ = lean_box(v_noDefaults_3809_);
v___x_3843_ = lean_box(v_star_3810_);
lean_inc(v_remove_3812_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3844_, 0, v_remove_3812_);
lean_closure_set(v___f_3844_, 1, v___x_3842_);
lean_closure_set(v___f_3844_, 2, v___x_3843_);
if (v_star_3810_ == 0)
{
v___y_3861_ = v_a_3814_;
v___y_3862_ = v_a_3815_;
v___y_3863_ = v_a_3816_;
v___y_3864_ = v_a_3817_;
goto v___jp_3860_;
}
else
{
if (v_noDefaults_3809_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v___f_3844_);
lean_dec_ref(v_use_3813_);
lean_dec(v_remove_3812_);
lean_dec(v_add_3811_);
v___x_3923_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_3924_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3923_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
else
{
v___y_3861_ = v_a_3814_;
v___y_3862_ = v_a_3815_;
v___y_3863_ = v_a_3816_;
v___y_3864_ = v_a_3817_;
goto v___jp_3860_;
}
}
v___jp_3819_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___y_3821_);
lean_ctor_set(v___x_3822_, 1, v___y_3820_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
v___jp_3824_:
{
uint8_t v___x_3831_; 
v___x_3831_ = l_List_isEmpty___redArg(v_remove_3812_);
lean_dec(v_remove_3812_);
if (v___x_3831_ == 0)
{
if (v_noDefaults_3809_ == 0)
{
v___y_3820_ = v___y_3826_;
v___y_3821_ = v___y_3830_;
goto v___jp_3819_;
}
else
{
if (v_star_3810_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3826_);
v___x_3832_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3833_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3832_, v___y_3829_, v___y_3828_, v___y_3825_, v___y_3827_);
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
else
{
v___y_3820_ = v___y_3826_;
v___y_3821_ = v___y_3830_;
goto v___jp_3819_;
}
}
}
else
{
v___y_3820_ = v___y_3826_;
v___y_3821_ = v___y_3830_;
goto v___jp_3819_;
}
}
v___jp_3845_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_array_to_list(v___y_3852_);
lean_inc(v___y_3850_);
v___x_3854_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3853_, v___y_3850_);
if (v_noDefaults_3809_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3811_, v___y_3850_);
v___x_3856_ = l_List_appendTR___redArg(v___x_3855_, v___x_3854_);
v___x_3857_ = l_List_appendTR___redArg(v___x_3856_, v___y_3851_);
v___y_3825_ = v___y_3846_;
v___y_3826_ = v___f_3844_;
v___y_3827_ = v___y_3847_;
v___y_3828_ = v___y_3849_;
v___y_3829_ = v___y_3848_;
v___y_3830_ = v___x_3857_;
goto v___jp_3824_;
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec(v___y_3851_);
v___x_3858_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3811_, v___y_3850_);
v___x_3859_ = l_List_appendTR___redArg(v___x_3858_, v___x_3854_);
v___y_3825_ = v___y_3846_;
v___y_3826_ = v___f_3844_;
v___y_3827_ = v___y_3847_;
v___y_3828_ = v___y_3849_;
v___y_3829_ = v___y_3848_;
v___y_3830_ = v___x_3859_;
goto v___jp_3824_;
}
}
v___jp_3860_:
{
lean_object* v_ref_3865_; lean_object* v_quotContext_3866_; lean_object* v_currMacroScope_3867_; lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; size_t v_sz_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v_ref_3865_ = lean_ctor_get(v___y_3863_, 5);
v_quotContext_3866_ = lean_ctor_get(v___y_3863_, 10);
v_currMacroScope_3867_ = lean_ctor_get(v___y_3863_, 11);
v___x_3868_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3868_);
v___x_3870_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_3871_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3867_, 2);
lean_inc_n(v_quotContext_3866_, 2);
v___x_3874_ = l_Lean_addMacroScope(v_quotContext_3866_, v___x_3873_, v_currMacroScope_3867_);
v___x_3875_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_3876_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref(v___x_3876_);
v___x_3878_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_3879_ = l_Lean_addMacroScope(v_quotContext_3866_, v___x_3878_, v_currMacroScope_3867_);
v___x_3880_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_3881_ = lean_array_size(v_use_3813_);
v___x_3882_ = ((size_t)0ULL);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3881_, v___x_3882_, v_use_3813_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3867_, 2);
lean_inc_n(v_quotContext_3866_, 2);
v___x_3886_ = l_Lean_addMacroScope(v_quotContext_3866_, v___x_3885_, v_currMacroScope_3867_);
v___x_3887_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_3888_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_3889_ = l_Lean_addMacroScope(v_quotContext_3866_, v___x_3888_, v_currMacroScope_3867_);
v___x_3890_ = 0;
v___x_3891_ = l_Lean_SourceInfo_fromRef(v_ref_3865_, v___x_3890_);
v___x_3892_ = lean_box(0);
v___x_3893_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_3894_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3891_);
lean_ctor_set(v___x_3894_, 1, v___x_3870_);
lean_ctor_set(v___x_3894_, 2, v___x_3874_);
lean_ctor_set(v___x_3894_, 3, v___x_3893_);
v___x_3895_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_3896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3896_, 0, v_a_3869_);
lean_ctor_set(v___x_3896_, 1, v___x_3875_);
lean_ctor_set(v___x_3896_, 2, v___x_3879_);
lean_ctor_set(v___x_3896_, 3, v___x_3895_);
v___x_3897_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_3898_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3898_, 0, v_a_3872_);
lean_ctor_set(v___x_3898_, 1, v___x_3880_);
lean_ctor_set(v___x_3898_, 2, v___x_3886_);
lean_ctor_set(v___x_3898_, 3, v___x_3897_);
v___x_3899_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_3900_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3900_, 0, v_a_3877_);
lean_ctor_set(v___x_3900_, 1, v___x_3887_);
lean_ctor_set(v___x_3900_, 2, v___x_3889_);
lean_ctor_set(v___x_3900_, 3, v___x_3899_);
v___x_3901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
lean_ctor_set(v___x_3901_, 1, v___x_3892_);
v___x_3902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3898_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3896_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3894_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_3904_, v___x_3892_);
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_3908_ = lean_array_get_size(v_a_3884_);
v___x_3909_ = lean_nat_dec_lt(v___x_3906_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_dec(v_a_3884_);
v___y_3846_ = v___y_3863_;
v___y_3847_ = v___y_3864_;
v___y_3848_ = v___y_3861_;
v___y_3849_ = v___y_3862_;
v___y_3850_ = v___x_3892_;
v___y_3851_ = v___x_3905_;
v___y_3852_ = v___x_3907_;
goto v___jp_3845_;
}
else
{
uint8_t v___x_3910_; 
v___x_3910_ = lean_nat_dec_le(v___x_3908_, v___x_3908_);
if (v___x_3910_ == 0)
{
if (v___x_3909_ == 0)
{
lean_dec(v_a_3884_);
v___y_3846_ = v___y_3863_;
v___y_3847_ = v___y_3864_;
v___y_3848_ = v___y_3861_;
v___y_3849_ = v___y_3862_;
v___y_3850_ = v___x_3892_;
v___y_3851_ = v___x_3905_;
v___y_3852_ = v___x_3907_;
goto v___jp_3845_;
}
else
{
size_t v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_usize_of_nat(v___x_3908_);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3884_, v___x_3882_, v___x_3911_, v___x_3907_);
lean_dec(v_a_3884_);
v___y_3846_ = v___y_3863_;
v___y_3847_ = v___y_3864_;
v___y_3848_ = v___y_3861_;
v___y_3849_ = v___y_3862_;
v___y_3850_ = v___x_3892_;
v___y_3851_ = v___x_3905_;
v___y_3852_ = v___x_3912_;
goto v___jp_3845_;
}
}
else
{
size_t v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_usize_of_nat(v___x_3908_);
v___x_3914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_3884_, v___x_3882_, v___x_3913_, v___x_3907_);
lean_dec(v_a_3884_);
v___y_3846_ = v___y_3863_;
v___y_3847_ = v___y_3864_;
v___y_3848_ = v___y_3861_;
v___y_3849_ = v___y_3862_;
v___y_3850_ = v___x_3892_;
v___y_3851_ = v___x_3905_;
v___y_3852_ = v___x_3914_;
goto v___jp_3845_;
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v___x_3879_);
lean_dec(v_a_3877_);
lean_dec(v___x_3874_);
lean_dec(v_a_3872_);
lean_dec(v_a_3869_);
lean_dec_ref(v___f_3844_);
lean_dec(v_remove_3812_);
lean_dec(v_add_3811_);
v_a_3915_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3883_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3883_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_3933_, lean_object* v_star_3934_, lean_object* v_add_3935_, lean_object* v_remove_3936_, lean_object* v_use_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
uint8_t v_noDefaults_boxed_3943_; uint8_t v_star_boxed_3944_; lean_object* v_res_3945_; 
v_noDefaults_boxed_3943_ = lean_unbox(v_noDefaults_3933_);
v_star_boxed_3944_ = lean_unbox(v_star_3934_);
v_res_3945_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_3943_, v_star_boxed_3944_, v_add_3935_, v_remove_3936_, v_use_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_3946_, size_t v_i_3947_, lean_object* v_bs_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_3946_, v_i_3947_, v_bs_3948_, v___y_3951_, v___y_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_3955_, lean_object* v_i_3956_, lean_object* v_bs_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
size_t v_sz_boxed_3963_; size_t v_i_boxed_3964_; lean_object* v_res_3965_; 
v_sz_boxed_3963_ = lean_unbox_usize(v_sz_3955_);
lean_dec(v_sz_3955_);
v_i_boxed_3964_ = lean_unbox_usize(v_i_3956_);
lean_dec(v_i_3956_);
v_res_3965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_3963_, v_i_boxed_3964_, v_bs_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
return v_res_3965_;
}
}
lean_object* runtime_initialize_Init_Data_Sum(uint8_t builtin);
lean_object* runtime_initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Sum(uint8_t builtin);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Sum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_SolveByElim(builtin);
}
#ifdef __cplusplus
}
#endif
