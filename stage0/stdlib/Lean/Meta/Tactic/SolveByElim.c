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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2;
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
static const lean_closure_object l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hasMVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_142_);
if (lean_obj_tag(v_val_144_) == 1)
{
uint8_t v_v_145_; 
v_v_145_ = lean_ctor_get_uint8(v_val_144_, 0);
lean_dec_ref(v_val_144_);
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
lean_dec_ref(v___x_157_);
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
lean_dec_ref(v___x_274_);
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
uint8_t v___x_14186__boxed_297_; uint8_t v___x_14187__boxed_298_; lean_object* v_res_299_; 
v___x_14186__boxed_297_ = lean_unbox(v___x_288_);
v___x_14187__boxed_298_ = lean_unbox(v___x_289_);
v_res_299_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_14186__boxed_297_, v___x_14187__boxed_298_, v_x_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v_x_300_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v_x_300_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v_x_300_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set_tag(v___x_304_, 1);
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v_x_300_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v_x_300_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v_x_300_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 0);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg___boxed(lean_object* v_x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_318_);
return v_res_320_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_e_321_){
_start:
{
if (lean_obj_tag(v_e_321_) == 0)
{
uint8_t v___x_322_; 
v___x_322_ = 2;
return v___x_322_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = 0;
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_e_324_){
_start:
{
uint8_t v_res_325_; lean_object* v_r_326_; 
v_res_325_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_e_324_);
lean_dec_ref(v_e_324_);
v_r_326_ = lean_box(v_res_325_);
return v_r_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_327_, lean_object* v_opt_328_){
_start:
{
lean_object* v_name_329_; lean_object* v_defValue_330_; lean_object* v_map_331_; lean_object* v___x_332_; 
v_name_329_ = lean_ctor_get(v_opt_328_, 0);
v_defValue_330_ = lean_ctor_get(v_opt_328_, 1);
v_map_331_ = lean_ctor_get(v_opts_327_, 0);
v___x_332_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_331_, v_name_329_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_inc(v_defValue_330_);
return v_defValue_330_;
}
else
{
lean_object* v_val_333_; 
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref(v___x_332_);
if (lean_obj_tag(v_val_333_) == 3)
{
lean_object* v_v_334_; 
v_v_334_ = lean_ctor_get(v_val_333_, 0);
lean_inc(v_v_334_);
lean_dec_ref(v_val_333_);
return v_v_334_;
}
else
{
lean_dec(v_val_333_);
lean_inc(v_defValue_330_);
return v_defValue_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_335_, lean_object* v_opt_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_335_, v_opt_336_);
lean_dec_ref(v_opt_336_);
lean_dec_ref(v_opts_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(size_t v_sz_338_, size_t v_i_339_, lean_object* v_bs_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_341_ == 0)
{
return v_bs_340_;
}
else
{
lean_object* v_v_342_; lean_object* v_msg_343_; lean_object* v___x_344_; lean_object* v_bs_x27_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v_v_342_ = lean_array_uget_borrowed(v_bs_340_, v_i_339_);
v_msg_343_ = lean_ctor_get(v_v_342_, 1);
lean_inc_ref(v_msg_343_);
v___x_344_ = lean_unsigned_to_nat(0u);
v_bs_x27_345_ = lean_array_uset(v_bs_340_, v_i_339_, v___x_344_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_339_, v___x_346_);
v___x_348_ = lean_array_uset(v_bs_x27_345_, v_i_339_, v_msg_343_);
v_i_339_ = v___x_347_;
v_bs_340_ = v___x_348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_bs_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_354_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_boxed_353_, v_i_boxed_354_, v_bs_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(lean_object* v_msgData_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_env_363_; lean_object* v___x_364_; lean_object* v_mctx_365_; lean_object* v_lctx_366_; lean_object* v_options_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_362_ = lean_st_ref_get(v___y_360_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_362_);
v___x_364_ = lean_st_ref_get(v___y_358_);
v_mctx_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_mctx_365_);
lean_dec(v___x_364_);
v_lctx_366_ = lean_ctor_get(v___y_357_, 2);
v_options_367_ = lean_ctor_get(v___y_359_, 2);
lean_inc_ref(v_options_367_);
lean_inc_ref(v_lctx_366_);
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v_env_363_);
lean_ctor_set(v___x_368_, 1, v_mctx_365_);
lean_ctor_set(v___x_368_, 2, v_lctx_366_);
lean_ctor_set(v___x_368_, 3, v_options_367_);
v___x_369_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_msgData_356_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6___boxed(lean_object* v_msgData_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msgData_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_oldTraces_378_, lean_object* v_data_379_, lean_object* v_ref_380_, lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_fileName_387_; lean_object* v_fileMap_388_; lean_object* v_options_389_; lean_object* v_currRecDepth_390_; lean_object* v_maxRecDepth_391_; lean_object* v_ref_392_; lean_object* v_currNamespace_393_; lean_object* v_openDecls_394_; lean_object* v_initHeartbeats_395_; lean_object* v_maxHeartbeats_396_; lean_object* v_quotContext_397_; lean_object* v_currMacroScope_398_; uint8_t v_diag_399_; lean_object* v_cancelTk_x3f_400_; uint8_t v_suppressElabErrors_401_; lean_object* v_inheritedTraceOptions_402_; lean_object* v___x_403_; lean_object* v_traceState_404_; lean_object* v_traces_405_; lean_object* v_ref_406_; lean_object* v___x_407_; lean_object* v___x_408_; size_t v_sz_409_; size_t v___x_410_; lean_object* v___x_411_; lean_object* v_msg_412_; lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_451_; 
v_fileName_387_ = lean_ctor_get(v___y_384_, 0);
v_fileMap_388_ = lean_ctor_get(v___y_384_, 1);
v_options_389_ = lean_ctor_get(v___y_384_, 2);
v_currRecDepth_390_ = lean_ctor_get(v___y_384_, 3);
v_maxRecDepth_391_ = lean_ctor_get(v___y_384_, 4);
v_ref_392_ = lean_ctor_get(v___y_384_, 5);
v_currNamespace_393_ = lean_ctor_get(v___y_384_, 6);
v_openDecls_394_ = lean_ctor_get(v___y_384_, 7);
v_initHeartbeats_395_ = lean_ctor_get(v___y_384_, 8);
v_maxHeartbeats_396_ = lean_ctor_get(v___y_384_, 9);
v_quotContext_397_ = lean_ctor_get(v___y_384_, 10);
v_currMacroScope_398_ = lean_ctor_get(v___y_384_, 11);
v_diag_399_ = lean_ctor_get_uint8(v___y_384_, sizeof(void*)*14);
v_cancelTk_x3f_400_ = lean_ctor_get(v___y_384_, 12);
v_suppressElabErrors_401_ = lean_ctor_get_uint8(v___y_384_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_402_ = lean_ctor_get(v___y_384_, 13);
v___x_403_ = lean_st_ref_get(v___y_385_);
v_traceState_404_ = lean_ctor_get(v___x_403_, 4);
lean_inc_ref(v_traceState_404_);
lean_dec(v___x_403_);
v_traces_405_ = lean_ctor_get(v_traceState_404_, 0);
lean_inc_ref(v_traces_405_);
lean_dec_ref(v_traceState_404_);
v_ref_406_ = l_Lean_replaceRef(v_ref_380_, v_ref_392_);
lean_inc_ref(v_inheritedTraceOptions_402_);
lean_inc(v_cancelTk_x3f_400_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc(v_maxRecDepth_391_);
lean_inc(v_currRecDepth_390_);
lean_inc_ref(v_options_389_);
lean_inc_ref(v_fileMap_388_);
lean_inc_ref(v_fileName_387_);
v___x_407_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_407_, 0, v_fileName_387_);
lean_ctor_set(v___x_407_, 1, v_fileMap_388_);
lean_ctor_set(v___x_407_, 2, v_options_389_);
lean_ctor_set(v___x_407_, 3, v_currRecDepth_390_);
lean_ctor_set(v___x_407_, 4, v_maxRecDepth_391_);
lean_ctor_set(v___x_407_, 5, v_ref_406_);
lean_ctor_set(v___x_407_, 6, v_currNamespace_393_);
lean_ctor_set(v___x_407_, 7, v_openDecls_394_);
lean_ctor_set(v___x_407_, 8, v_initHeartbeats_395_);
lean_ctor_set(v___x_407_, 9, v_maxHeartbeats_396_);
lean_ctor_set(v___x_407_, 10, v_quotContext_397_);
lean_ctor_set(v___x_407_, 11, v_currMacroScope_398_);
lean_ctor_set(v___x_407_, 12, v_cancelTk_x3f_400_);
lean_ctor_set(v___x_407_, 13, v_inheritedTraceOptions_402_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*14, v_diag_399_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*14 + 1, v_suppressElabErrors_401_);
v___x_408_ = l_Lean_PersistentArray_toArray___redArg(v_traces_405_);
lean_dec_ref(v_traces_405_);
v_sz_409_ = lean_array_size(v___x_408_);
v___x_410_ = ((size_t)0ULL);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_409_, v___x_410_, v___x_408_);
v_msg_412_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_412_, 0, v_data_379_);
lean_ctor_set(v_msg_412_, 1, v_msg_381_);
lean_ctor_set(v_msg_412_, 2, v___x_411_);
v___x_413_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_412_, v___y_382_, v___y_383_, v___x_407_, v___y_385_);
lean_dec_ref(v___x_407_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_451_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_451_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_451_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_traceState_419_; lean_object* v_env_420_; lean_object* v_nextMacroScope_421_; lean_object* v_ngen_422_; lean_object* v_auxDeclNGen_423_; lean_object* v_cache_424_; lean_object* v_messages_425_; lean_object* v_infoState_426_; lean_object* v_snapshotTasks_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_450_; 
v___x_418_ = lean_st_ref_take(v___y_385_);
v_traceState_419_ = lean_ctor_get(v___x_418_, 4);
v_env_420_ = lean_ctor_get(v___x_418_, 0);
v_nextMacroScope_421_ = lean_ctor_get(v___x_418_, 1);
v_ngen_422_ = lean_ctor_get(v___x_418_, 2);
v_auxDeclNGen_423_ = lean_ctor_get(v___x_418_, 3);
v_cache_424_ = lean_ctor_get(v___x_418_, 5);
v_messages_425_ = lean_ctor_get(v___x_418_, 6);
v_infoState_426_ = lean_ctor_get(v___x_418_, 7);
v_snapshotTasks_427_ = lean_ctor_get(v___x_418_, 8);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_450_ == 0)
{
v___x_429_ = v___x_418_;
v_isShared_430_ = v_isSharedCheck_450_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snapshotTasks_427_);
lean_inc(v_infoState_426_);
lean_inc(v_messages_425_);
lean_inc(v_cache_424_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_423_);
lean_inc(v_ngen_422_);
lean_inc(v_nextMacroScope_421_);
lean_inc(v_env_420_);
lean_dec(v___x_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_450_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint64_t v_tid_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_448_; 
v_tid_431_ = lean_ctor_get_uint64(v_traceState_419_, sizeof(void*)*1);
v_isSharedCheck_448_ = !lean_is_exclusive(v_traceState_419_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v_traceState_419_, 0);
lean_dec(v_unused_449_);
v___x_433_ = v_traceState_419_;
v_isShared_434_ = v_isSharedCheck_448_;
goto v_resetjp_432_;
}
else
{
lean_dec(v_traceState_419_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_448_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_ref_380_);
lean_ctor_set(v___x_435_, 1, v_a_414_);
v___x_436_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_378_, v___x_435_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_436_);
v___x_438_ = v___x_433_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_436_);
lean_ctor_set_uint64(v_reuseFailAlloc_447_, sizeof(void*)*1, v_tid_431_);
v___x_438_ = v_reuseFailAlloc_447_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 4, v___x_438_);
v___x_440_ = v___x_429_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_env_420_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_nextMacroScope_421_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_ngen_422_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_auxDeclNGen_423_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v_cache_424_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_messages_425_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_infoState_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v_snapshotTasks_427_);
v___x_440_ = v_reuseFailAlloc_446_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = lean_st_ref_set(v___y_385_, v___x_440_);
v___x_442_ = lean_box(0);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_442_);
v___x_444_ = v___x_416_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_oldTraces_452_, lean_object* v_data_453_, lean_object* v_ref_454_, lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_452_, v_data_453_, v_ref_454_, v_msg_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_461_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_465_; double v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_float_of_nat(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5(void){
_start:
{
lean_object* v___x_470_; double v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(1000u);
v___x_471_ = lean_float_of_nat(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_472_, uint8_t v_collapsed_473_, lean_object* v_tag_474_, lean_object* v_opts_475_, uint8_t v_clsEnabled_476_, lean_object* v_oldTraces_477_, lean_object* v_msg_478_, lean_object* v_resStartStop_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_584_; 
v_fst_485_ = lean_ctor_get(v_resStartStop_479_, 0);
v_snd_486_ = lean_ctor_get(v_resStartStop_479_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_resStartStop_479_);
if (v_isSharedCheck_584_ == 0)
{
v___x_488_ = v_resStartStop_479_;
v_isShared_489_ = v_isSharedCheck_584_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_486_);
lean_inc(v_fst_485_);
lean_dec(v_resStartStop_479_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_584_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_data_493_; lean_object* v_fst_504_; lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_583_; 
v_fst_504_ = lean_ctor_get(v_snd_486_, 0);
v_snd_505_ = lean_ctor_get(v_snd_486_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_486_);
if (v_isSharedCheck_583_ == 0)
{
v___x_507_ = v_snd_486_;
v_isShared_508_ = v_isSharedCheck_583_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_504_);
lean_dec(v_snd_486_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_583_;
goto v_resetjp_506_;
}
v___jp_490_:
{
lean_object* v___x_494_; 
lean_inc(v___y_492_);
v___x_494_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_477_, v_data_493_, v___y_492_, v___y_491_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_dec_ref(v___x_494_);
v___x_495_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_485_);
return v___x_495_;
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_fst_485_);
v_a_496_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_494_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
v_resetjp_506_:
{
lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___y_512_; lean_object* v_a_513_; uint8_t v___y_537_; double v___y_568_; 
v___x_509_ = l_Lean_trace_profiler;
v___x_510_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_475_, v___x_509_);
if (v___x_510_ == 0)
{
v___y_537_ = v___x_510_;
goto v___jp_536_;
}
else
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = l_Lean_trace_profiler_useHeartbeats;
v___x_574_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_475_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; double v___x_577_; double v___x_578_; double v___x_579_; 
v___x_575_ = l_Lean_trace_profiler_threshold;
v___x_576_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_475_, v___x_575_);
v___x_577_ = lean_float_of_nat(v___x_576_);
v___x_578_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5);
v___x_579_ = lean_float_div(v___x_577_, v___x_578_);
v___y_568_ = v___x_579_;
goto v___jp_567_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; double v___x_582_; 
v___x_580_ = l_Lean_trace_profiler_threshold;
v___x_581_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_475_, v___x_580_);
v___x_582_ = lean_float_of_nat(v___x_581_);
v___y_568_ = v___x_582_;
goto v___jp_567_;
}
}
v___jp_511_:
{
uint8_t v_result_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v_result_514_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_fst_485_);
v___x_515_ = l_Lean_TraceResult_toEmoji(v_result_514_);
v___x_516_ = l_Lean_stringToMessageData(v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 7);
lean_ctor_set(v___x_507_, 1, v___x_517_);
lean_ctor_set(v___x_507_, 0, v___x_516_);
v___x_519_ = v___x_507_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_517_);
v___x_519_ = v_reuseFailAlloc_530_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v_m_521_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 7);
lean_ctor_set(v___x_488_, 1, v_a_513_);
lean_ctor_set(v___x_488_, 0, v___x_519_);
v_m_521_ = v___x_488_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_a_513_);
v_m_521_ = v_reuseFailAlloc_529_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; double v___x_524_; lean_object* v_data_525_; 
v___x_522_ = lean_box(v_result_514_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
v___x_524_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
lean_inc_ref(v_tag_474_);
lean_inc_ref(v___x_523_);
lean_inc(v_cls_472_);
v_data_525_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_525_, 0, v_cls_472_);
lean_ctor_set(v_data_525_, 1, v___x_523_);
lean_ctor_set(v_data_525_, 2, v_tag_474_);
lean_ctor_set_float(v_data_525_, sizeof(void*)*3, v___x_524_);
lean_ctor_set_float(v_data_525_, sizeof(void*)*3 + 8, v___x_524_);
lean_ctor_set_uint8(v_data_525_, sizeof(void*)*3 + 16, v_collapsed_473_);
if (v___x_510_ == 0)
{
lean_dec_ref(v___x_523_);
lean_dec(v_snd_505_);
lean_dec(v_fst_504_);
lean_dec_ref(v_tag_474_);
lean_dec(v_cls_472_);
v___y_491_ = v_m_521_;
v___y_492_ = v___y_512_;
v_data_493_ = v_data_525_;
goto v___jp_490_;
}
else
{
lean_object* v_data_526_; double v___x_527_; double v___x_528_; 
lean_dec_ref(v_data_525_);
v_data_526_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_526_, 0, v_cls_472_);
lean_ctor_set(v_data_526_, 1, v___x_523_);
lean_ctor_set(v_data_526_, 2, v_tag_474_);
v___x_527_ = lean_unbox_float(v_fst_504_);
lean_dec(v_fst_504_);
lean_ctor_set_float(v_data_526_, sizeof(void*)*3, v___x_527_);
v___x_528_ = lean_unbox_float(v_snd_505_);
lean_dec(v_snd_505_);
lean_ctor_set_float(v_data_526_, sizeof(void*)*3 + 8, v___x_528_);
lean_ctor_set_uint8(v_data_526_, sizeof(void*)*3 + 16, v_collapsed_473_);
v___y_491_ = v_m_521_;
v___y_492_ = v___y_512_;
v_data_493_ = v_data_526_;
goto v___jp_490_;
}
}
}
}
v___jp_531_:
{
lean_object* v_ref_532_; lean_object* v___x_533_; 
v_ref_532_ = lean_ctor_get(v___y_482_, 5);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v___y_481_);
lean_inc_ref(v___y_480_);
lean_inc(v_fst_485_);
v___x_533_ = lean_apply_6(v_msg_478_, v_fst_485_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, lean_box(0));
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref(v___x_533_);
v___y_512_ = v_ref_532_;
v_a_513_ = v_a_534_;
goto v___jp_511_;
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v___x_533_);
v___x_535_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4);
v___y_512_ = v_ref_532_;
v_a_513_ = v___x_535_;
goto v___jp_511_;
}
}
v___jp_536_:
{
if (v_clsEnabled_476_ == 0)
{
if (v___y_537_ == 0)
{
lean_object* v___x_538_; lean_object* v_traceState_539_; lean_object* v_env_540_; lean_object* v_nextMacroScope_541_; lean_object* v_ngen_542_; lean_object* v_auxDeclNGen_543_; lean_object* v_cache_544_; lean_object* v_messages_545_; lean_object* v_infoState_546_; lean_object* v_snapshotTasks_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_566_; 
lean_del_object(v___x_507_);
lean_dec(v_snd_505_);
lean_dec(v_fst_504_);
lean_del_object(v___x_488_);
lean_dec_ref(v_msg_478_);
lean_dec_ref(v_tag_474_);
lean_dec(v_cls_472_);
v___x_538_ = lean_st_ref_take(v___y_483_);
v_traceState_539_ = lean_ctor_get(v___x_538_, 4);
v_env_540_ = lean_ctor_get(v___x_538_, 0);
v_nextMacroScope_541_ = lean_ctor_get(v___x_538_, 1);
v_ngen_542_ = lean_ctor_get(v___x_538_, 2);
v_auxDeclNGen_543_ = lean_ctor_get(v___x_538_, 3);
v_cache_544_ = lean_ctor_get(v___x_538_, 5);
v_messages_545_ = lean_ctor_get(v___x_538_, 6);
v_infoState_546_ = lean_ctor_get(v___x_538_, 7);
v_snapshotTasks_547_ = lean_ctor_get(v___x_538_, 8);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_566_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_566_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snapshotTasks_547_);
lean_inc(v_infoState_546_);
lean_inc(v_messages_545_);
lean_inc(v_cache_544_);
lean_inc(v_traceState_539_);
lean_inc(v_auxDeclNGen_543_);
lean_inc(v_ngen_542_);
lean_inc(v_nextMacroScope_541_);
lean_inc(v_env_540_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_566_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint64_t v_tid_551_; lean_object* v_traces_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_565_; 
v_tid_551_ = lean_ctor_get_uint64(v_traceState_539_, sizeof(void*)*1);
v_traces_552_ = lean_ctor_get(v_traceState_539_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_traceState_539_);
if (v_isSharedCheck_565_ == 0)
{
v___x_554_ = v_traceState_539_;
v_isShared_555_ = v_isSharedCheck_565_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_traces_552_);
lean_dec(v_traceState_539_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_565_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_477_, v_traces_552_);
lean_dec_ref(v_traces_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_556_);
lean_ctor_set_uint64(v_reuseFailAlloc_564_, sizeof(void*)*1, v_tid_551_);
v___x_558_ = v_reuseFailAlloc_564_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 4, v___x_558_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_env_540_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_nextMacroScope_541_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_auxDeclNGen_543_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_563_, 5, v_cache_544_);
lean_ctor_set(v_reuseFailAlloc_563_, 6, v_messages_545_);
lean_ctor_set(v_reuseFailAlloc_563_, 7, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_563_, 8, v_snapshotTasks_547_);
v___x_560_ = v_reuseFailAlloc_563_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_st_ref_set(v___y_483_, v___x_560_);
v___x_562_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_485_);
return v___x_562_;
}
}
}
}
}
else
{
goto v___jp_531_;
}
}
else
{
goto v___jp_531_;
}
}
v___jp_567_:
{
double v___x_569_; double v___x_570_; double v___x_571_; uint8_t v___x_572_; 
v___x_569_ = lean_unbox_float(v_snd_505_);
v___x_570_ = lean_unbox_float(v_fst_504_);
v___x_571_ = lean_float_sub(v___x_569_, v___x_570_);
v___x_572_ = lean_float_decLt(v___y_568_, v___x_571_);
v___y_537_ = v___x_572_;
goto v___jp_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_585_, lean_object* v_collapsed_586_, lean_object* v_tag_587_, lean_object* v_opts_588_, lean_object* v_clsEnabled_589_, lean_object* v_oldTraces_590_, lean_object* v_msg_591_, lean_object* v_resStartStop_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v_collapsed_boxed_598_; uint8_t v_clsEnabled_boxed_599_; lean_object* v_res_600_; 
v_collapsed_boxed_598_ = lean_unbox(v_collapsed_586_);
v_clsEnabled_boxed_599_ = lean_unbox(v_clsEnabled_589_);
v_res_600_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_585_, v_collapsed_boxed_598_, v_tag_587_, v_opts_588_, v_clsEnabled_boxed_599_, v_oldTraces_590_, v_msg_591_, v_resStartStop_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v_opts_588_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_x_603_);
return v___x_609_;
}
else
{
lean_object* v_head_610_; lean_object* v_tail_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_634_; 
v_head_610_ = lean_ctor_get(v_x_602_, 0);
v_tail_611_ = lean_ctor_get(v_x_602_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_634_ == 0)
{
v___x_613_ = v_x_602_;
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_tail_611_);
lean_inc(v_head_610_);
lean_dec(v_x_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_634_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; 
lean_inc(v_head_610_);
v___x_615_ = l_Lean_MVarId_inferInstance(v_head_610_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_dec_ref(v___x_615_);
lean_del_object(v___x_613_);
lean_dec(v_head_610_);
v_x_602_ = v_tail_611_;
goto _start;
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_633_; 
v_a_617_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_633_ == 0)
{
v___x_619_ = v___x_615_;
v_isShared_620_ = v_isSharedCheck_633_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_633_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___y_622_; uint8_t v___x_631_; 
v___x_631_ = l_Lean_Exception_isInterrupt(v_a_617_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; 
lean_inc(v_a_617_);
v___x_632_ = l_Lean_Exception_isRuntime(v_a_617_);
v___y_622_ = v___x_632_;
goto v___jp_621_;
}
else
{
v___y_622_ = v___x_631_;
goto v___jp_621_;
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_del_object(v___x_619_);
lean_dec(v_a_617_);
if (v___x_601_ == 0)
{
lean_del_object(v___x_613_);
lean_dec(v_head_610_);
v_x_602_ = v_tail_611_;
goto _start;
}
else
{
lean_object* v___x_625_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v_x_603_);
v___x_625_ = v___x_613_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_head_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_x_603_);
v___x_625_ = v_reuseFailAlloc_627_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v_x_602_ = v_tail_611_;
v_x_603_ = v___x_625_;
goto _start;
}
}
}
else
{
lean_object* v___x_629_; 
lean_del_object(v___x_613_);
lean_dec(v_tail_611_);
lean_dec(v_head_610_);
lean_dec(v_x_603_);
if (v_isShared_620_ == 0)
{
v___x_629_ = v___x_619_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_617_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v___x_14652__boxed_643_; lean_object* v_res_644_; 
v___x_14652__boxed_643_ = lean_unbox(v___x_635_);
v_res_644_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14652__boxed_643_, v_x_636_, v_x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_x_647_);
return v___x_653_;
}
else
{
lean_object* v_head_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_678_; 
v_head_654_ = lean_ctor_get(v_x_646_, 0);
v_tail_655_ = lean_ctor_get(v_x_646_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_678_ == 0)
{
v___x_657_ = v_x_646_;
v_isShared_658_ = v_isSharedCheck_678_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_head_654_);
lean_dec(v_x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_678_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_664_; 
lean_inc(v_head_654_);
v___x_664_ = l_Lean_MVarId_inferInstance(v_head_654_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_dec_ref(v___x_664_);
if (v___x_645_ == 0)
{
lean_del_object(v___x_657_);
lean_dec(v_head_654_);
v_x_646_ = v_tail_655_;
goto _start;
}
else
{
goto v___jp_659_;
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_677_; 
v_a_666_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_677_ == 0)
{
v___x_668_ = v___x_664_;
v_isShared_669_ = v_isSharedCheck_677_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_677_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
uint8_t v___y_671_; uint8_t v___x_675_; 
v___x_675_ = l_Lean_Exception_isInterrupt(v_a_666_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; 
lean_inc(v_a_666_);
v___x_676_ = l_Lean_Exception_isRuntime(v_a_666_);
v___y_671_ = v___x_676_;
goto v___jp_670_;
}
else
{
v___y_671_ = v___x_675_;
goto v___jp_670_;
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
lean_del_object(v___x_668_);
lean_dec(v_a_666_);
goto v___jp_659_;
}
else
{
lean_object* v___x_673_; 
lean_del_object(v___x_657_);
lean_dec(v_tail_655_);
lean_dec(v_head_654_);
lean_dec(v_x_647_);
if (v_isShared_669_ == 0)
{
v___x_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_666_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
v___jp_659_:
{
lean_object* v___x_661_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_x_647_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_head_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_x_647_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_x_646_ = v_tail_655_;
v_x_647_ = v___x_661_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___x_14729__boxed_687_; lean_object* v_res_688_; 
v___x_14729__boxed_687_ = lean_unbox(v___x_679_);
v_res_688_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14729__boxed_687_, v_x_680_, v_x_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_688_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_692_; double v___x_693_; 
v___x_692_ = lean_unsigned_to_nat(1000000000u);
v___x_693_ = lean_float_of_nat(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_694_, lean_object* v_g_695_, lean_object* v_e_696_, lean_object* v_cfg_697_, lean_object* v___x_698_, lean_object* v___x_699_, uint8_t v___x_700_, lean_object* v___x_701_, lean_object* v___f_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_options_708_; uint8_t v_hasTrace_709_; 
v_options_708_ = lean_ctor_get(v___y_705_, 2);
v_hasTrace_709_ = lean_ctor_get_uint8(v_options_708_, sizeof(void*)*1);
if (v_hasTrace_709_ == 0)
{
lean_object* v___x_710_; uint8_t v_foApprox_711_; uint8_t v_ctxApprox_712_; uint8_t v_quasiPatternApprox_713_; uint8_t v_constApprox_714_; uint8_t v_isDefEqStuckEx_715_; uint8_t v_unificationHints_716_; uint8_t v_proofIrrelevance_717_; uint8_t v_assignSyntheticOpaque_718_; uint8_t v_offsetCnstrs_719_; uint8_t v_etaStruct_720_; uint8_t v_univApprox_721_; uint8_t v_iota_722_; uint8_t v_beta_723_; uint8_t v_proj_724_; uint8_t v_zeta_725_; uint8_t v_zetaDelta_726_; uint8_t v_zetaUnused_727_; uint8_t v_zetaHave_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v___f_702_);
lean_dec_ref(v___x_701_);
lean_dec(v___x_699_);
v___x_710_ = l_Lean_Meta_Context_config(v___y_703_);
v_foApprox_711_ = lean_ctor_get_uint8(v___x_710_, 0);
v_ctxApprox_712_ = lean_ctor_get_uint8(v___x_710_, 1);
v_quasiPatternApprox_713_ = lean_ctor_get_uint8(v___x_710_, 2);
v_constApprox_714_ = lean_ctor_get_uint8(v___x_710_, 3);
v_isDefEqStuckEx_715_ = lean_ctor_get_uint8(v___x_710_, 4);
v_unificationHints_716_ = lean_ctor_get_uint8(v___x_710_, 5);
v_proofIrrelevance_717_ = lean_ctor_get_uint8(v___x_710_, 6);
v_assignSyntheticOpaque_718_ = lean_ctor_get_uint8(v___x_710_, 7);
v_offsetCnstrs_719_ = lean_ctor_get_uint8(v___x_710_, 8);
v_etaStruct_720_ = lean_ctor_get_uint8(v___x_710_, 10);
v_univApprox_721_ = lean_ctor_get_uint8(v___x_710_, 11);
v_iota_722_ = lean_ctor_get_uint8(v___x_710_, 12);
v_beta_723_ = lean_ctor_get_uint8(v___x_710_, 13);
v_proj_724_ = lean_ctor_get_uint8(v___x_710_, 14);
v_zeta_725_ = lean_ctor_get_uint8(v___x_710_, 15);
v_zetaDelta_726_ = lean_ctor_get_uint8(v___x_710_, 16);
v_zetaUnused_727_ = lean_ctor_get_uint8(v___x_710_, 17);
v_zetaHave_728_ = lean_ctor_get_uint8(v___x_710_, 18);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_766_ == 0)
{
v___x_730_ = v___x_710_;
v_isShared_731_ = v_isSharedCheck_766_;
goto v_resetjp_729_;
}
else
{
lean_dec(v___x_710_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_766_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
uint8_t v_trackZetaDelta_732_; lean_object* v_zetaDeltaSet_733_; lean_object* v_lctx_734_; lean_object* v_localInstances_735_; lean_object* v_defEqCtx_x3f_736_; lean_object* v_synthPendingDepth_737_; lean_object* v_canUnfold_x3f_738_; uint8_t v_univApprox_739_; uint8_t v_inTypeClassResolution_740_; uint8_t v_cacheInferType_741_; lean_object* v_config_743_; 
v_trackZetaDelta_732_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7);
v_zetaDeltaSet_733_ = lean_ctor_get(v___y_703_, 1);
v_lctx_734_ = lean_ctor_get(v___y_703_, 2);
v_localInstances_735_ = lean_ctor_get(v___y_703_, 3);
v_defEqCtx_x3f_736_ = lean_ctor_get(v___y_703_, 4);
v_synthPendingDepth_737_ = lean_ctor_get(v___y_703_, 5);
v_canUnfold_x3f_738_ = lean_ctor_get(v___y_703_, 6);
v_univApprox_739_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_740_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 2);
v_cacheInferType_741_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 3);
if (v_isShared_731_ == 0)
{
v_config_743_ = v___x_730_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 0, v_foApprox_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 1, v_ctxApprox_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 2, v_quasiPatternApprox_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 3, v_constApprox_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 4, v_isDefEqStuckEx_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 5, v_unificationHints_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 6, v_proofIrrelevance_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 7, v_assignSyntheticOpaque_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 8, v_offsetCnstrs_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 10, v_etaStruct_720_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 11, v_univApprox_721_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 12, v_iota_722_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 13, v_beta_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 14, v_proj_724_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 15, v_zeta_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 16, v_zetaDelta_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 17, v_zetaUnused_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_765_, 18, v_zetaHave_728_);
v_config_743_ = v_reuseFailAlloc_765_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
uint64_t v___x_744_; uint64_t v___x_745_; uint64_t v___x_746_; uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v_key_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_ctor_set_uint8(v_config_743_, 9, v_transparency_694_);
v___x_744_ = l_Lean_Meta_Context_configKey(v___y_703_);
v___x_745_ = 2ULL;
v___x_746_ = lean_uint64_shift_right(v___x_744_, v___x_745_);
v___x_747_ = lean_uint64_shift_left(v___x_746_, v___x_745_);
v___x_748_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_694_);
v_key_749_ = lean_uint64_lor(v___x_747_, v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_750_, 0, v_config_743_);
lean_ctor_set_uint64(v___x_750_, sizeof(void*)*1, v_key_749_);
lean_inc(v_canUnfold_x3f_738_);
lean_inc(v_synthPendingDepth_737_);
lean_inc(v_defEqCtx_x3f_736_);
lean_inc_ref(v_localInstances_735_);
lean_inc_ref(v_lctx_734_);
lean_inc(v_zetaDeltaSet_733_);
v___x_751_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v_zetaDeltaSet_733_);
lean_ctor_set(v___x_751_, 2, v_lctx_734_);
lean_ctor_set(v___x_751_, 3, v_localInstances_735_);
lean_ctor_set(v___x_751_, 4, v_defEqCtx_x3f_736_);
lean_ctor_set(v___x_751_, 5, v_synthPendingDepth_737_);
lean_ctor_set(v___x_751_, 6, v_canUnfold_x3f_738_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*7, v_trackZetaDelta_732_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*7 + 1, v_univApprox_739_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*7 + 2, v_inTypeClassResolution_740_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*7 + 3, v_cacheInferType_741_);
v___x_752_ = l_Lean_MVarId_apply(v_g_695_, v_e_696_, v_cfg_697_, v___x_698_, v___x_751_, v___y_704_, v___y_705_, v___y_706_);
lean_dec_ref(v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref(v___x_752_);
v___x_754_ = lean_box(0);
v___x_755_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_709_, v_a_753_, v___x_754_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = l_List_reverse___redArg(v_a_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
return v___x_755_;
}
}
else
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v_a_774_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v_a_789_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v_a_807_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v_a_819_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; 
v_inheritedTraceOptions_767_ = lean_ctor_get(v___y_705_, 13);
v___x_768_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_699_);
v___x_769_ = l_Lean_Name_append(v___x_768_, v___x_699_);
v___x_770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_767_, v_options_708_, v___x_769_);
lean_dec(v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_941_ = l_Lean_trace_profiler;
v___x_942_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_708_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; uint8_t v_foApprox_944_; uint8_t v_ctxApprox_945_; uint8_t v_quasiPatternApprox_946_; uint8_t v_constApprox_947_; uint8_t v_isDefEqStuckEx_948_; uint8_t v_unificationHints_949_; uint8_t v_proofIrrelevance_950_; uint8_t v_assignSyntheticOpaque_951_; uint8_t v_offsetCnstrs_952_; uint8_t v_etaStruct_953_; uint8_t v_univApprox_954_; uint8_t v_iota_955_; uint8_t v_beta_956_; uint8_t v_proj_957_; uint8_t v_zeta_958_; uint8_t v_zetaDelta_959_; uint8_t v_zetaUnused_960_; uint8_t v_zetaHave_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_999_; 
lean_dec_ref(v___f_702_);
lean_dec_ref(v___x_701_);
lean_dec(v___x_699_);
v___x_943_ = l_Lean_Meta_Context_config(v___y_703_);
v_foApprox_944_ = lean_ctor_get_uint8(v___x_943_, 0);
v_ctxApprox_945_ = lean_ctor_get_uint8(v___x_943_, 1);
v_quasiPatternApprox_946_ = lean_ctor_get_uint8(v___x_943_, 2);
v_constApprox_947_ = lean_ctor_get_uint8(v___x_943_, 3);
v_isDefEqStuckEx_948_ = lean_ctor_get_uint8(v___x_943_, 4);
v_unificationHints_949_ = lean_ctor_get_uint8(v___x_943_, 5);
v_proofIrrelevance_950_ = lean_ctor_get_uint8(v___x_943_, 6);
v_assignSyntheticOpaque_951_ = lean_ctor_get_uint8(v___x_943_, 7);
v_offsetCnstrs_952_ = lean_ctor_get_uint8(v___x_943_, 8);
v_etaStruct_953_ = lean_ctor_get_uint8(v___x_943_, 10);
v_univApprox_954_ = lean_ctor_get_uint8(v___x_943_, 11);
v_iota_955_ = lean_ctor_get_uint8(v___x_943_, 12);
v_beta_956_ = lean_ctor_get_uint8(v___x_943_, 13);
v_proj_957_ = lean_ctor_get_uint8(v___x_943_, 14);
v_zeta_958_ = lean_ctor_get_uint8(v___x_943_, 15);
v_zetaDelta_959_ = lean_ctor_get_uint8(v___x_943_, 16);
v_zetaUnused_960_ = lean_ctor_get_uint8(v___x_943_, 17);
v_zetaHave_961_ = lean_ctor_get_uint8(v___x_943_, 18);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_999_ == 0)
{
v___x_963_ = v___x_943_;
v_isShared_964_ = v_isSharedCheck_999_;
goto v_resetjp_962_;
}
else
{
lean_dec(v___x_943_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_999_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v_trackZetaDelta_965_; lean_object* v_zetaDeltaSet_966_; lean_object* v_lctx_967_; lean_object* v_localInstances_968_; lean_object* v_defEqCtx_x3f_969_; lean_object* v_synthPendingDepth_970_; lean_object* v_canUnfold_x3f_971_; uint8_t v_univApprox_972_; uint8_t v_inTypeClassResolution_973_; uint8_t v_cacheInferType_974_; lean_object* v_config_976_; 
v_trackZetaDelta_965_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7);
v_zetaDeltaSet_966_ = lean_ctor_get(v___y_703_, 1);
v_lctx_967_ = lean_ctor_get(v___y_703_, 2);
v_localInstances_968_ = lean_ctor_get(v___y_703_, 3);
v_defEqCtx_x3f_969_ = lean_ctor_get(v___y_703_, 4);
v_synthPendingDepth_970_ = lean_ctor_get(v___y_703_, 5);
v_canUnfold_x3f_971_ = lean_ctor_get(v___y_703_, 6);
v_univApprox_972_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_973_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 2);
v_cacheInferType_974_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 3);
if (v_isShared_964_ == 0)
{
v_config_976_ = v___x_963_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 0, v_foApprox_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 1, v_ctxApprox_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 2, v_quasiPatternApprox_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 3, v_constApprox_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 4, v_isDefEqStuckEx_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 5, v_unificationHints_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 6, v_proofIrrelevance_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 7, v_assignSyntheticOpaque_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 8, v_offsetCnstrs_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 10, v_etaStruct_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 11, v_univApprox_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 12, v_iota_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 13, v_beta_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 14, v_proj_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 15, v_zeta_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 16, v_zetaDelta_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 17, v_zetaUnused_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, 18, v_zetaHave_961_);
v_config_976_ = v_reuseFailAlloc_998_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
uint64_t v___x_977_; uint64_t v___x_978_; uint64_t v___x_979_; uint64_t v___x_980_; uint64_t v___x_981_; uint64_t v_key_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_ctor_set_uint8(v_config_976_, 9, v_transparency_694_);
v___x_977_ = l_Lean_Meta_Context_configKey(v___y_703_);
v___x_978_ = 2ULL;
v___x_979_ = lean_uint64_shift_right(v___x_977_, v___x_978_);
v___x_980_ = lean_uint64_shift_left(v___x_979_, v___x_978_);
v___x_981_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_694_);
v_key_982_ = lean_uint64_lor(v___x_980_, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_983_, 0, v_config_976_);
lean_ctor_set_uint64(v___x_983_, sizeof(void*)*1, v_key_982_);
lean_inc(v_canUnfold_x3f_971_);
lean_inc(v_synthPendingDepth_970_);
lean_inc(v_defEqCtx_x3f_969_);
lean_inc_ref(v_localInstances_968_);
lean_inc_ref(v_lctx_967_);
lean_inc(v_zetaDeltaSet_966_);
v___x_984_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_zetaDeltaSet_966_);
lean_ctor_set(v___x_984_, 2, v_lctx_967_);
lean_ctor_set(v___x_984_, 3, v_localInstances_968_);
lean_ctor_set(v___x_984_, 4, v_defEqCtx_x3f_969_);
lean_ctor_set(v___x_984_, 5, v_synthPendingDepth_970_);
lean_ctor_set(v___x_984_, 6, v_canUnfold_x3f_971_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*7, v_trackZetaDelta_965_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*7 + 1, v_univApprox_972_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*7 + 2, v_inTypeClassResolution_973_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*7 + 3, v_cacheInferType_974_);
v___x_985_ = l_Lean_MVarId_apply(v_g_695_, v_e_696_, v_cfg_697_, v___x_698_, v___x_984_, v___y_704_, v___y_705_, v___y_706_);
lean_dec_ref(v___x_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_box(0);
v___x_988_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_942_, v_hasTrace_709_, v_a_986_, v___x_987_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = l_List_reverse___redArg(v_a_989_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
return v___x_988_;
}
}
else
{
return v___x_985_;
}
}
}
}
else
{
goto v___jp_834_;
}
}
else
{
goto v___jp_834_;
}
v___jp_771_:
{
lean_object* v___x_775_; double v___x_776_; double v___x_777_; double v___x_778_; double v___x_779_; double v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_775_ = lean_io_mono_nanos_now();
v___x_776_ = lean_float_of_nat(v___y_772_);
v___x_777_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_778_ = lean_float_div(v___x_776_, v___x_777_);
v___x_779_ = lean_float_of_nat(v___x_775_);
v___x_780_ = lean_float_div(v___x_779_, v___x_777_);
v___x_781_ = lean_box_float(v___x_778_);
v___x_782_ = lean_box_float(v___x_780_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_774_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_699_, v___x_700_, v___x_701_, v_options_708_, v___x_770_, v___y_773_, v___f_702_, v___x_784_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_785_;
}
v___jp_786_:
{
lean_object* v___x_790_; 
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v_a_789_);
v___y_772_ = v___y_787_;
v___y_773_ = v___y_788_;
v_a_774_ = v___x_790_;
goto v___jp_771_;
}
v___jp_791_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___y_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___y_794_);
v___y_787_ = v___y_792_;
v___y_788_ = v___y_793_;
v_a_789_ = v_a_795_;
goto v___jp_786_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___y_794_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___y_794_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___y_794_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___y_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v___y_772_ = v___y_792_;
v___y_773_ = v___y_793_;
v_a_774_ = v___x_801_;
goto v___jp_771_;
}
}
}
}
v___jp_804_:
{
lean_object* v___x_808_; double v___x_809_; double v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_808_ = lean_io_get_num_heartbeats();
v___x_809_ = lean_float_of_nat(v___y_805_);
v___x_810_ = lean_float_of_nat(v___x_808_);
v___x_811_ = lean_box_float(v___x_809_);
v___x_812_ = lean_box_float(v___x_810_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_a_807_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_699_, v___x_700_, v___x_701_, v_options_708_, v___x_770_, v___y_806_, v___f_702_, v___x_814_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_815_;
}
v___jp_816_:
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_a_819_);
v___y_805_ = v___y_817_;
v___y_806_ = v___y_818_;
v_a_807_ = v___x_820_;
goto v___jp_804_;
}
v___jp_821_:
{
if (lean_obj_tag(v___y_824_) == 0)
{
lean_object* v_a_825_; 
v_a_825_ = lean_ctor_get(v___y_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref(v___y_824_);
v___y_817_ = v___y_822_;
v___y_818_ = v___y_823_;
v_a_819_ = v_a_825_;
goto v___jp_816_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___y_824_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___y_824_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___y_824_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___y_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set_tag(v___x_828_, 0);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v___y_805_ = v___y_822_;
v___y_806_ = v___y_823_;
v_a_807_ = v___x_831_;
goto v___jp_804_;
}
}
}
}
v___jp_834_:
{
lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_706_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v___x_835_);
v___x_837_ = l_Lean_trace_profiler_useHeartbeats;
v___x_838_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_708_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v_foApprox_841_; uint8_t v_ctxApprox_842_; uint8_t v_quasiPatternApprox_843_; uint8_t v_constApprox_844_; uint8_t v_isDefEqStuckEx_845_; uint8_t v_unificationHints_846_; uint8_t v_proofIrrelevance_847_; uint8_t v_assignSyntheticOpaque_848_; uint8_t v_offsetCnstrs_849_; uint8_t v_etaStruct_850_; uint8_t v_univApprox_851_; uint8_t v_iota_852_; uint8_t v_beta_853_; uint8_t v_proj_854_; uint8_t v_zeta_855_; uint8_t v_zetaDelta_856_; uint8_t v_zetaUnused_857_; uint8_t v_zetaHave_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_889_; 
v___x_839_ = lean_io_mono_nanos_now();
v___x_840_ = l_Lean_Meta_Context_config(v___y_703_);
v_foApprox_841_ = lean_ctor_get_uint8(v___x_840_, 0);
v_ctxApprox_842_ = lean_ctor_get_uint8(v___x_840_, 1);
v_quasiPatternApprox_843_ = lean_ctor_get_uint8(v___x_840_, 2);
v_constApprox_844_ = lean_ctor_get_uint8(v___x_840_, 3);
v_isDefEqStuckEx_845_ = lean_ctor_get_uint8(v___x_840_, 4);
v_unificationHints_846_ = lean_ctor_get_uint8(v___x_840_, 5);
v_proofIrrelevance_847_ = lean_ctor_get_uint8(v___x_840_, 6);
v_assignSyntheticOpaque_848_ = lean_ctor_get_uint8(v___x_840_, 7);
v_offsetCnstrs_849_ = lean_ctor_get_uint8(v___x_840_, 8);
v_etaStruct_850_ = lean_ctor_get_uint8(v___x_840_, 10);
v_univApprox_851_ = lean_ctor_get_uint8(v___x_840_, 11);
v_iota_852_ = lean_ctor_get_uint8(v___x_840_, 12);
v_beta_853_ = lean_ctor_get_uint8(v___x_840_, 13);
v_proj_854_ = lean_ctor_get_uint8(v___x_840_, 14);
v_zeta_855_ = lean_ctor_get_uint8(v___x_840_, 15);
v_zetaDelta_856_ = lean_ctor_get_uint8(v___x_840_, 16);
v_zetaUnused_857_ = lean_ctor_get_uint8(v___x_840_, 17);
v_zetaHave_858_ = lean_ctor_get_uint8(v___x_840_, 18);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_889_ == 0)
{
v___x_860_ = v___x_840_;
v_isShared_861_ = v_isSharedCheck_889_;
goto v_resetjp_859_;
}
else
{
lean_dec(v___x_840_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_889_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
uint8_t v_trackZetaDelta_862_; lean_object* v_zetaDeltaSet_863_; lean_object* v_lctx_864_; lean_object* v_localInstances_865_; lean_object* v_defEqCtx_x3f_866_; lean_object* v_synthPendingDepth_867_; lean_object* v_canUnfold_x3f_868_; uint8_t v_univApprox_869_; uint8_t v_inTypeClassResolution_870_; uint8_t v_cacheInferType_871_; lean_object* v_config_873_; 
v_trackZetaDelta_862_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7);
v_zetaDeltaSet_863_ = lean_ctor_get(v___y_703_, 1);
v_lctx_864_ = lean_ctor_get(v___y_703_, 2);
v_localInstances_865_ = lean_ctor_get(v___y_703_, 3);
v_defEqCtx_x3f_866_ = lean_ctor_get(v___y_703_, 4);
v_synthPendingDepth_867_ = lean_ctor_get(v___y_703_, 5);
v_canUnfold_x3f_868_ = lean_ctor_get(v___y_703_, 6);
v_univApprox_869_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_870_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 2);
v_cacheInferType_871_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 3);
if (v_isShared_861_ == 0)
{
v_config_873_ = v___x_860_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 0, v_foApprox_841_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 1, v_ctxApprox_842_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 2, v_quasiPatternApprox_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 3, v_constApprox_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 4, v_isDefEqStuckEx_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 5, v_unificationHints_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 6, v_proofIrrelevance_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 7, v_assignSyntheticOpaque_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 8, v_offsetCnstrs_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 10, v_etaStruct_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 11, v_univApprox_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 12, v_iota_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 13, v_beta_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 14, v_proj_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 15, v_zeta_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 16, v_zetaDelta_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 17, v_zetaUnused_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, 18, v_zetaHave_858_);
v_config_873_ = v_reuseFailAlloc_888_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v_key_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_ctor_set_uint8(v_config_873_, 9, v_transparency_694_);
v___x_874_ = l_Lean_Meta_Context_configKey(v___y_703_);
v___x_875_ = 2ULL;
v___x_876_ = lean_uint64_shift_right(v___x_874_, v___x_875_);
v___x_877_ = lean_uint64_shift_left(v___x_876_, v___x_875_);
v___x_878_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_694_);
v_key_879_ = lean_uint64_lor(v___x_877_, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_880_, 0, v_config_873_);
lean_ctor_set_uint64(v___x_880_, sizeof(void*)*1, v_key_879_);
lean_inc(v_canUnfold_x3f_868_);
lean_inc(v_synthPendingDepth_867_);
lean_inc(v_defEqCtx_x3f_866_);
lean_inc_ref(v_localInstances_865_);
lean_inc_ref(v_lctx_864_);
lean_inc(v_zetaDeltaSet_863_);
v___x_881_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v_zetaDeltaSet_863_);
lean_ctor_set(v___x_881_, 2, v_lctx_864_);
lean_ctor_set(v___x_881_, 3, v_localInstances_865_);
lean_ctor_set(v___x_881_, 4, v_defEqCtx_x3f_866_);
lean_ctor_set(v___x_881_, 5, v_synthPendingDepth_867_);
lean_ctor_set(v___x_881_, 6, v_canUnfold_x3f_868_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*7, v_trackZetaDelta_862_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*7 + 1, v_univApprox_869_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*7 + 2, v_inTypeClassResolution_870_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*7 + 3, v_cacheInferType_871_);
v___x_882_ = l_Lean_MVarId_apply(v_g_695_, v_e_696_, v_cfg_697_, v___x_698_, v___x_881_, v___y_704_, v___y_705_, v___y_706_);
lean_dec_ref(v___x_881_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___x_884_ = lean_box(0);
v___x_885_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_838_, v_hasTrace_709_, v_a_883_, v___x_884_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v___x_887_ = l_List_reverse___redArg(v_a_886_);
v___y_787_ = v___x_839_;
v___y_788_ = v_a_836_;
v_a_789_ = v___x_887_;
goto v___jp_786_;
}
else
{
v___y_792_ = v___x_839_;
v___y_793_ = v_a_836_;
v___y_794_ = v___x_885_;
goto v___jp_791_;
}
}
else
{
v___y_792_ = v___x_839_;
v___y_793_ = v_a_836_;
v___y_794_ = v___x_882_;
goto v___jp_791_;
}
}
}
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v_foApprox_892_; uint8_t v_ctxApprox_893_; uint8_t v_quasiPatternApprox_894_; uint8_t v_constApprox_895_; uint8_t v_isDefEqStuckEx_896_; uint8_t v_unificationHints_897_; uint8_t v_proofIrrelevance_898_; uint8_t v_assignSyntheticOpaque_899_; uint8_t v_offsetCnstrs_900_; uint8_t v_etaStruct_901_; uint8_t v_univApprox_902_; uint8_t v_iota_903_; uint8_t v_beta_904_; uint8_t v_proj_905_; uint8_t v_zeta_906_; uint8_t v_zetaDelta_907_; uint8_t v_zetaUnused_908_; uint8_t v_zetaHave_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_940_; 
v___x_890_ = lean_io_get_num_heartbeats();
v___x_891_ = l_Lean_Meta_Context_config(v___y_703_);
v_foApprox_892_ = lean_ctor_get_uint8(v___x_891_, 0);
v_ctxApprox_893_ = lean_ctor_get_uint8(v___x_891_, 1);
v_quasiPatternApprox_894_ = lean_ctor_get_uint8(v___x_891_, 2);
v_constApprox_895_ = lean_ctor_get_uint8(v___x_891_, 3);
v_isDefEqStuckEx_896_ = lean_ctor_get_uint8(v___x_891_, 4);
v_unificationHints_897_ = lean_ctor_get_uint8(v___x_891_, 5);
v_proofIrrelevance_898_ = lean_ctor_get_uint8(v___x_891_, 6);
v_assignSyntheticOpaque_899_ = lean_ctor_get_uint8(v___x_891_, 7);
v_offsetCnstrs_900_ = lean_ctor_get_uint8(v___x_891_, 8);
v_etaStruct_901_ = lean_ctor_get_uint8(v___x_891_, 10);
v_univApprox_902_ = lean_ctor_get_uint8(v___x_891_, 11);
v_iota_903_ = lean_ctor_get_uint8(v___x_891_, 12);
v_beta_904_ = lean_ctor_get_uint8(v___x_891_, 13);
v_proj_905_ = lean_ctor_get_uint8(v___x_891_, 14);
v_zeta_906_ = lean_ctor_get_uint8(v___x_891_, 15);
v_zetaDelta_907_ = lean_ctor_get_uint8(v___x_891_, 16);
v_zetaUnused_908_ = lean_ctor_get_uint8(v___x_891_, 17);
v_zetaHave_909_ = lean_ctor_get_uint8(v___x_891_, 18);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_940_ == 0)
{
v___x_911_ = v___x_891_;
v_isShared_912_ = v_isSharedCheck_940_;
goto v_resetjp_910_;
}
else
{
lean_dec(v___x_891_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_940_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v_trackZetaDelta_913_; lean_object* v_zetaDeltaSet_914_; lean_object* v_lctx_915_; lean_object* v_localInstances_916_; lean_object* v_defEqCtx_x3f_917_; lean_object* v_synthPendingDepth_918_; lean_object* v_canUnfold_x3f_919_; uint8_t v_univApprox_920_; uint8_t v_inTypeClassResolution_921_; uint8_t v_cacheInferType_922_; lean_object* v_config_924_; 
v_trackZetaDelta_913_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7);
v_zetaDeltaSet_914_ = lean_ctor_get(v___y_703_, 1);
v_lctx_915_ = lean_ctor_get(v___y_703_, 2);
v_localInstances_916_ = lean_ctor_get(v___y_703_, 3);
v_defEqCtx_x3f_917_ = lean_ctor_get(v___y_703_, 4);
v_synthPendingDepth_918_ = lean_ctor_get(v___y_703_, 5);
v_canUnfold_x3f_919_ = lean_ctor_get(v___y_703_, 6);
v_univApprox_920_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_921_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 2);
v_cacheInferType_922_ = lean_ctor_get_uint8(v___y_703_, sizeof(void*)*7 + 3);
if (v_isShared_912_ == 0)
{
v_config_924_ = v___x_911_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 0, v_foApprox_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 1, v_ctxApprox_893_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 2, v_quasiPatternApprox_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 3, v_constApprox_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 4, v_isDefEqStuckEx_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 5, v_unificationHints_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 6, v_proofIrrelevance_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 7, v_assignSyntheticOpaque_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 8, v_offsetCnstrs_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 10, v_etaStruct_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 11, v_univApprox_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 12, v_iota_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 13, v_beta_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 14, v_proj_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 15, v_zeta_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 16, v_zetaDelta_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 17, v_zetaUnused_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, 18, v_zetaHave_909_);
v_config_924_ = v_reuseFailAlloc_939_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
uint64_t v___x_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v___x_928_; uint64_t v___x_929_; uint64_t v_key_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_ctor_set_uint8(v_config_924_, 9, v_transparency_694_);
v___x_925_ = l_Lean_Meta_Context_configKey(v___y_703_);
v___x_926_ = 2ULL;
v___x_927_ = lean_uint64_shift_right(v___x_925_, v___x_926_);
v___x_928_ = lean_uint64_shift_left(v___x_927_, v___x_926_);
v___x_929_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_694_);
v_key_930_ = lean_uint64_lor(v___x_928_, v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_931_, 0, v_config_924_);
lean_ctor_set_uint64(v___x_931_, sizeof(void*)*1, v_key_930_);
lean_inc(v_canUnfold_x3f_919_);
lean_inc(v_synthPendingDepth_918_);
lean_inc(v_defEqCtx_x3f_917_);
lean_inc_ref(v_localInstances_916_);
lean_inc_ref(v_lctx_915_);
lean_inc(v_zetaDeltaSet_914_);
v___x_932_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v_zetaDeltaSet_914_);
lean_ctor_set(v___x_932_, 2, v_lctx_915_);
lean_ctor_set(v___x_932_, 3, v_localInstances_916_);
lean_ctor_set(v___x_932_, 4, v_defEqCtx_x3f_917_);
lean_ctor_set(v___x_932_, 5, v_synthPendingDepth_918_);
lean_ctor_set(v___x_932_, 6, v_canUnfold_x3f_919_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*7, v_trackZetaDelta_913_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*7 + 1, v_univApprox_920_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*7 + 2, v_inTypeClassResolution_921_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*7 + 3, v_cacheInferType_922_);
v___x_933_ = l_Lean_MVarId_apply(v_g_695_, v_e_696_, v_cfg_697_, v___x_698_, v___x_932_, v___y_704_, v___y_705_, v___y_706_);
lean_dec_ref(v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = lean_box(0);
v___x_936_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_838_, v_a_934_, v___x_935_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = l_List_reverse___redArg(v_a_937_);
v___y_817_ = v___x_890_;
v___y_818_ = v_a_836_;
v_a_819_ = v___x_938_;
goto v___jp_816_;
}
else
{
v___y_822_ = v___x_890_;
v___y_823_ = v_a_836_;
v___y_824_ = v___x_936_;
goto v___jp_821_;
}
}
else
{
v___y_822_ = v___x_890_;
v___y_823_ = v_a_836_;
v___y_824_ = v___x_933_;
goto v___jp_821_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_1000_, lean_object* v_g_1001_, lean_object* v_e_1002_, lean_object* v_cfg_1003_, lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v___f_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v_transparency_boxed_1014_; uint8_t v___x_14817__boxed_1015_; lean_object* v_res_1016_; 
v_transparency_boxed_1014_ = lean_unbox(v_transparency_1000_);
v___x_14817__boxed_1015_ = lean_unbox(v___x_1006_);
v_res_1016_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_1014_, v_g_1001_, v_e_1002_, v_cfg_1003_, v___x_1004_, v___x_1005_, v___x_14817__boxed_1015_, v___x_1007_, v___f_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_1018_, lean_object* v_g_1019_, lean_object* v_cfg_1020_, lean_object* v_e_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; 
lean_inc_ref(v_e_1021_);
v___f_1027_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1027_, 0, v_e_1021_);
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1029_ = lean_box(0);
v___x_1030_ = 1;
v___x_1031_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1032_ = lean_box(v_transparency_1018_);
v___x_1033_ = lean_box(v___x_1030_);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1034_, 0, v___x_1032_);
lean_closure_set(v___f_1034_, 1, v_g_1019_);
lean_closure_set(v___f_1034_, 2, v_e_1021_);
lean_closure_set(v___f_1034_, 3, v_cfg_1020_);
lean_closure_set(v___f_1034_, 4, v___x_1029_);
lean_closure_set(v___f_1034_, 5, v___x_1028_);
lean_closure_set(v___f_1034_, 6, v___x_1033_);
lean_closure_set(v___f_1034_, 7, v___x_1031_);
lean_closure_set(v___f_1034_, 8, v___f_1027_);
v___x_1035_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_1034_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1036_, lean_object* v_g_1037_, lean_object* v_cfg_1038_, lean_object* v_e_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v_transparency_boxed_1045_; lean_object* v_res_1046_; 
v_transparency_boxed_1045_ = lean_unbox(v_transparency_1036_);
v_res_1046_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1045_, v_g_1037_, v_cfg_1038_, v_e_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1047_, uint8_t v_transparency_1048_, lean_object* v_lemmas_1049_, lean_object* v_g_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1049_, v_a_1051_, v_a_1052_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1065_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1065_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1065_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
v___x_1059_ = lean_box(v_transparency_1048_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1060_, 0, v___x_1059_);
lean_closure_set(v___f_1060_, 1, v_g_1050_);
lean_closure_set(v___f_1060_, 2, v_cfg_1047_);
v___x_1061_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1061_, 0, lean_box(0));
lean_closure_set(v___x_1061_, 1, lean_box(0));
lean_closure_set(v___x_1061_, 2, v___f_1060_);
lean_closure_set(v___x_1061_, 3, v_a_1055_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1061_);
v___x_1063_ = v___x_1057_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_g_1050_);
lean_dec_ref(v_cfg_1047_);
v_a_1066_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1054_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1054_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1074_, lean_object* v_transparency_1075_, lean_object* v_lemmas_1076_, lean_object* v_g_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
uint8_t v_transparency_boxed_1081_; lean_object* v_res_1082_; 
v_transparency_boxed_1081_ = lean_unbox(v_transparency_1075_);
v_res_1082_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1074_, v_transparency_boxed_1081_, v_lemmas_1076_, v_g_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec(v_a_1078_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1083_, uint8_t v_transparency_1084_, lean_object* v_lemmas_1085_, lean_object* v_g_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1083_, v_transparency_1084_, v_lemmas_1085_, v_g_1086_, v_a_1088_, v_a_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1093_, lean_object* v_transparency_1094_, lean_object* v_lemmas_1095_, lean_object* v_g_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
uint8_t v_transparency_boxed_1102_; lean_object* v_res_1103_; 
v_transparency_boxed_1102_ = lean_unbox(v_transparency_1094_);
v_res_1103_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1093_, v_transparency_boxed_1102_, v_lemmas_1095_, v_g_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_00_u03b1_1104_, lean_object* v_x_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_1105_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_00_u03b1_1112_, v_x_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1120_, uint8_t v_transparency_1121_, lean_object* v_lemmas_1122_, lean_object* v_g_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1120_, v_transparency_1121_, v_lemmas_1122_, v_g_1123_, v_a_1125_, v_a_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l_Lean_Meta_Iterator_head___redArg(v_a_1130_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
return v___x_1131_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1129_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1129_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1140_, lean_object* v_transparency_1141_, lean_object* v_lemmas_1142_, lean_object* v_g_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
uint8_t v_transparency_boxed_1149_; lean_object* v_res_1150_; 
v_transparency_boxed_1149_ = lean_unbox(v_transparency_1141_);
v_res_1150_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1140_, v_transparency_boxed_1149_, v_lemmas_1142_, v_g_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1151_){
_start:
{
lean_object* v_toApplyRulesConfig_1152_; lean_object* v_toBacktrackConfig_1153_; 
v_toApplyRulesConfig_1152_ = lean_ctor_get(v_x_1151_, 0);
v_toBacktrackConfig_1153_ = lean_ctor_get(v_toApplyRulesConfig_1152_, 0);
lean_inc_ref(v_toBacktrackConfig_1153_);
return v_toBacktrackConfig_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1154_);
lean_dec_ref(v_x_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1158_, lean_object* v_discharge_1159_, lean_object* v_g_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
lean_inc(v___y_1162_);
lean_inc_ref(v___y_1161_);
lean_inc(v_g_1160_);
v___x_1166_ = lean_apply_6(v_test_1158_, v_g_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, lean_box(0));
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1177_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_unbox(v_a_1167_);
lean_dec(v_a_1167_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_del_object(v___x_1169_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
lean_inc(v___y_1162_);
lean_inc_ref(v___y_1161_);
v___x_1172_ = lean_apply_6(v_discharge_1159_, v_g_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, lean_box(0));
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
lean_dec(v_g_1160_);
lean_dec_ref(v_discharge_1159_);
v___x_1173_ = lean_box(0);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1173_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_g_1160_);
lean_dec_ref(v_discharge_1159_);
v_a_1178_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1166_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1166_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1186_, lean_object* v_discharge_1187_, lean_object* v_g_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1186_, v_discharge_1187_, v_g_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1195_, lean_object* v_test_1196_){
_start:
{
lean_object* v_toApplyRulesConfig_1197_; lean_object* v_toBacktrackConfig_1198_; uint8_t v_backtracking_1199_; uint8_t v_intro_1200_; uint8_t v_constructor_1201_; uint8_t v_suggestions_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1234_; 
v_toApplyRulesConfig_1197_ = lean_ctor_get(v_cfg_1195_, 0);
lean_inc_ref(v_toApplyRulesConfig_1197_);
v_toBacktrackConfig_1198_ = lean_ctor_get(v_toApplyRulesConfig_1197_, 0);
lean_inc_ref(v_toBacktrackConfig_1198_);
v_backtracking_1199_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1);
v_intro_1200_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1 + 1);
v_constructor_1201_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1 + 2);
v_suggestions_1202_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*1 + 3);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_cfg_1195_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_cfg_1195_, 0);
lean_dec(v_unused_1235_);
v___x_1204_ = v_cfg_1195_;
v_isShared_1205_ = v_isSharedCheck_1234_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v_cfg_1195_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1234_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_toApplyConfig_1206_; uint8_t v_transparency_1207_; uint8_t v_symm_1208_; uint8_t v_exfalso_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1232_; 
v_toApplyConfig_1206_ = lean_ctor_get(v_toApplyRulesConfig_1197_, 1);
v_transparency_1207_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1197_, sizeof(void*)*2);
v_symm_1208_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1197_, sizeof(void*)*2 + 1);
v_exfalso_1209_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1197_, sizeof(void*)*2 + 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_toApplyRulesConfig_1197_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v_toApplyRulesConfig_1197_, 0);
lean_dec(v_unused_1233_);
v___x_1211_ = v_toApplyRulesConfig_1197_;
v_isShared_1212_ = v_isSharedCheck_1232_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_toApplyConfig_1206_);
lean_dec(v_toApplyRulesConfig_1197_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1232_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_maxDepth_1213_; lean_object* v_proc_1214_; lean_object* v_suspend_1215_; lean_object* v_discharge_1216_; uint8_t v_commitIndependentGoals_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1231_; 
v_maxDepth_1213_ = lean_ctor_get(v_toBacktrackConfig_1198_, 0);
v_proc_1214_ = lean_ctor_get(v_toBacktrackConfig_1198_, 1);
v_suspend_1215_ = lean_ctor_get(v_toBacktrackConfig_1198_, 2);
v_discharge_1216_ = lean_ctor_get(v_toBacktrackConfig_1198_, 3);
v_commitIndependentGoals_1217_ = lean_ctor_get_uint8(v_toBacktrackConfig_1198_, sizeof(void*)*4);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_toBacktrackConfig_1198_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1219_ = v_toBacktrackConfig_1198_;
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_discharge_1216_);
lean_inc(v_suspend_1215_);
lean_inc(v_proc_1214_);
lean_inc(v_maxDepth_1213_);
lean_dec(v_toBacktrackConfig_1198_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1231_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___f_1221_; lean_object* v___x_1223_; 
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1221_, 0, v_test_1196_);
lean_closure_set(v___f_1221_, 1, v_discharge_1216_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 3, v___f_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_maxDepth_1213_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_proc_1214_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_suspend_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v___f_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*4, v_commitIndependentGoals_1217_);
v___x_1223_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1225_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1223_);
v___x_1225_ = v___x_1211_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_toApplyConfig_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*2, v_transparency_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*2 + 1, v_symm_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1229_, sizeof(void*)*2 + 2, v_exfalso_1209_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1225_);
v___x_1227_ = v___x_1204_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1, v_backtracking_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1 + 1, v_intro_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1 + 2, v_constructor_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1228_, sizeof(void*)*1 + 3, v_suggestions_1202_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1236_, lean_object* v_proc_1237_, lean_object* v_orig_1238_, lean_object* v_goals_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
if (lean_obj_tag(v_goals_1239_) == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref(v_proc_1237_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
v___x_1245_ = lean_apply_7(v_proc_1236_, v_orig_1238_, v_goals_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, lean_box(0));
return v___x_1245_;
}
else
{
lean_object* v_head_1246_; lean_object* v_tail_1247_; lean_object* v___x_1248_; 
v_head_1246_ = lean_ctor_get(v_goals_1239_, 0);
v_tail_1247_ = lean_ctor_get(v_goals_1239_, 1);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v_head_1246_);
v___x_1248_ = lean_apply_6(v_proc_1237_, v_head_1246_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
lean_inc(v_tail_1247_);
lean_dec_ref(v_goals_1239_);
lean_dec(v_orig_1238_);
lean_dec_ref(v_proc_1236_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = l_List_appendTR___redArg(v_a_1249_, v_tail_1247_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1271_; 
v_a_1259_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1261_ = v___x_1248_;
v_isShared_1262_ = v_isSharedCheck_1271_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1248_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1271_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___y_1264_; uint8_t v___x_1269_; 
v___x_1269_ = l_Lean_Exception_isInterrupt(v_a_1259_);
if (v___x_1269_ == 0)
{
uint8_t v___x_1270_; 
lean_inc(v_a_1259_);
v___x_1270_ = l_Lean_Exception_isRuntime(v_a_1259_);
v___y_1264_ = v___x_1270_;
goto v___jp_1263_;
}
else
{
v___y_1264_ = v___x_1269_;
goto v___jp_1263_;
}
v___jp_1263_:
{
if (v___y_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_del_object(v___x_1261_);
lean_dec(v_a_1259_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
v___x_1265_ = lean_apply_7(v_proc_1236_, v_orig_1238_, v_goals_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, lean_box(0));
return v___x_1265_;
}
else
{
lean_object* v___x_1267_; 
lean_dec_ref(v_goals_1239_);
lean_dec(v_orig_1238_);
lean_dec_ref(v_proc_1236_);
if (v_isShared_1262_ == 0)
{
v___x_1267_ = v___x_1261_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1259_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1272_, lean_object* v_proc_1273_, lean_object* v_orig_1274_, lean_object* v_goals_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1272_, v_proc_1273_, v_orig_1274_, v_goals_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1282_, lean_object* v_proc_1283_){
_start:
{
lean_object* v_toApplyRulesConfig_1284_; lean_object* v_toBacktrackConfig_1285_; uint8_t v_backtracking_1286_; uint8_t v_intro_1287_; uint8_t v_constructor_1288_; uint8_t v_suggestions_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1321_; 
v_toApplyRulesConfig_1284_ = lean_ctor_get(v_cfg_1282_, 0);
lean_inc_ref(v_toApplyRulesConfig_1284_);
v_toBacktrackConfig_1285_ = lean_ctor_get(v_toApplyRulesConfig_1284_, 0);
lean_inc_ref(v_toBacktrackConfig_1285_);
v_backtracking_1286_ = lean_ctor_get_uint8(v_cfg_1282_, sizeof(void*)*1);
v_intro_1287_ = lean_ctor_get_uint8(v_cfg_1282_, sizeof(void*)*1 + 1);
v_constructor_1288_ = lean_ctor_get_uint8(v_cfg_1282_, sizeof(void*)*1 + 2);
v_suggestions_1289_ = lean_ctor_get_uint8(v_cfg_1282_, sizeof(void*)*1 + 3);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_cfg_1282_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_cfg_1282_, 0);
lean_dec(v_unused_1322_);
v___x_1291_ = v_cfg_1282_;
v_isShared_1292_ = v_isSharedCheck_1321_;
goto v_resetjp_1290_;
}
else
{
lean_dec(v_cfg_1282_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1321_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_toApplyConfig_1293_; uint8_t v_transparency_1294_; uint8_t v_symm_1295_; uint8_t v_exfalso_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1319_; 
v_toApplyConfig_1293_ = lean_ctor_get(v_toApplyRulesConfig_1284_, 1);
v_transparency_1294_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1284_, sizeof(void*)*2);
v_symm_1295_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1284_, sizeof(void*)*2 + 1);
v_exfalso_1296_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1284_, sizeof(void*)*2 + 2);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_toApplyRulesConfig_1284_);
if (v_isSharedCheck_1319_ == 0)
{
lean_object* v_unused_1320_; 
v_unused_1320_ = lean_ctor_get(v_toApplyRulesConfig_1284_, 0);
lean_dec(v_unused_1320_);
v___x_1298_ = v_toApplyRulesConfig_1284_;
v_isShared_1299_ = v_isSharedCheck_1319_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_toApplyConfig_1293_);
lean_dec(v_toApplyRulesConfig_1284_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1319_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_maxDepth_1300_; lean_object* v_proc_1301_; lean_object* v_suspend_1302_; lean_object* v_discharge_1303_; uint8_t v_commitIndependentGoals_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1318_; 
v_maxDepth_1300_ = lean_ctor_get(v_toBacktrackConfig_1285_, 0);
v_proc_1301_ = lean_ctor_get(v_toBacktrackConfig_1285_, 1);
v_suspend_1302_ = lean_ctor_get(v_toBacktrackConfig_1285_, 2);
v_discharge_1303_ = lean_ctor_get(v_toBacktrackConfig_1285_, 3);
v_commitIndependentGoals_1304_ = lean_ctor_get_uint8(v_toBacktrackConfig_1285_, sizeof(void*)*4);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_toBacktrackConfig_1285_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1306_ = v_toBacktrackConfig_1285_;
v_isShared_1307_ = v_isSharedCheck_1318_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_discharge_1303_);
lean_inc(v_suspend_1302_);
lean_inc(v_proc_1301_);
lean_inc(v_maxDepth_1300_);
lean_dec(v_toBacktrackConfig_1285_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1318_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___f_1308_; lean_object* v___x_1310_; 
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1308_, 0, v_proc_1301_);
lean_closure_set(v___f_1308_, 1, v_proc_1283_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___f_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_maxDepth_1300_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___f_1308_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_suspend_1302_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_discharge_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*4, v_commitIndependentGoals_1304_);
v___x_1310_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1310_);
v___x_1312_ = v___x_1298_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_toApplyConfig_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*2, v_transparency_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*2 + 1, v_symm_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*2 + 2, v_exfalso_1296_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1312_);
v___x_1314_ = v___x_1291_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, sizeof(void*)*1, v_backtracking_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, sizeof(void*)*1 + 1, v_intro_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, sizeof(void*)*1 + 2, v_constructor_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1315_, sizeof(void*)*1 + 3, v_suggestions_1289_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = 1;
v___x_1330_ = l_Lean_Meta_intro1Core(v_g_1323_, v___x_1329_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1348_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1348_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1348_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1346_; 
v_snd_1335_ = lean_ctor_get(v_a_1331_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_a_1331_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_a_1331_, 0);
lean_dec(v_unused_1347_);
v___x_1337_ = v_a_1331_;
v_isShared_1338_ = v_isSharedCheck_1346_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_dec(v_a_1331_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1346_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_box(0);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 1);
lean_ctor_set(v___x_1337_, 1, v___x_1339_);
lean_ctor_set(v___x_1337_, 0, v_snd_1335_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_snd_1335_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1341_);
v___x_1343_ = v___x_1333_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1330_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1330_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1365_){
_start:
{
lean_object* v___f_1366_; lean_object* v___x_1367_; 
v___f_1366_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1367_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1365_, v___f_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_ks_1372_; lean_object* v_vs_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1397_; 
v_ks_1372_ = lean_ctor_get(v_x_1368_, 0);
v_vs_1373_ = lean_ctor_get(v_x_1368_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1368_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1375_ = v_x_1368_;
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_vs_1373_);
lean_inc(v_ks_1372_);
lean_dec(v_x_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_ks_1372_);
v___x_1378_ = lean_nat_dec_lt(v_x_1369_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec(v_x_1369_);
v___x_1379_ = lean_array_push(v_ks_1372_, v_x_1370_);
v___x_1380_ = lean_array_push(v_vs_1373_, v_x_1371_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1380_);
lean_ctor_set(v___x_1375_, 0, v___x_1379_);
v___x_1382_ = v___x_1375_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
lean_object* v_k_x27_1384_; uint8_t v___x_1385_; 
v_k_x27_1384_ = lean_array_fget_borrowed(v_ks_1372_, v_x_1369_);
v___x_1385_ = l_Lean_instBEqMVarId_beq(v_x_1370_, v_k_x27_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1387_; 
if (v_isShared_1376_ == 0)
{
v___x_1387_ = v___x_1375_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_ks_1372_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_vs_1373_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = lean_nat_add(v_x_1369_, v___x_1388_);
lean_dec(v_x_1369_);
v_x_1368_ = v___x_1387_;
v_x_1369_ = v___x_1389_;
goto _start;
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_array_fset(v_ks_1372_, v_x_1369_, v_x_1370_);
v___x_1393_ = lean_array_fset(v_vs_1373_, v_x_1369_, v_x_1371_);
lean_dec(v_x_1369_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1393_);
lean_ctor_set(v___x_1375_, 0, v___x_1392_);
v___x_1395_ = v___x_1375_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1398_, lean_object* v_k_1399_, lean_object* v_v_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1398_, v___x_1401_, v_k_1399_, v_v_1400_);
return v___x_1402_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; 
v___x_1403_ = ((size_t)5ULL);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_shift_left(v___x_1404_, v___x_1403_);
return v___x_1405_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1406_; size_t v___x_1407_; size_t v___x_1408_; 
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1408_ = lean_usize_sub(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1410_, size_t v_x_1411_, size_t v_x_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v_es_1415_; size_t v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; size_t v___x_1419_; lean_object* v_j_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_es_1415_ = lean_ctor_get(v_x_1410_, 0);
v___x_1416_ = ((size_t)5ULL);
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1419_ = lean_usize_land(v_x_1411_, v___x_1418_);
v_j_1420_ = lean_usize_to_nat(v___x_1419_);
v___x_1421_ = lean_array_get_size(v_es_1415_);
v___x_1422_ = lean_nat_dec_lt(v_j_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_dec(v_j_1420_);
lean_dec(v_x_1414_);
lean_dec(v_x_1413_);
return v_x_1410_;
}
else
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1459_; 
lean_inc_ref(v_es_1415_);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_x_1410_, 0);
lean_dec(v_unused_1460_);
v___x_1424_ = v_x_1410_;
v_isShared_1425_ = v_isSharedCheck_1459_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v_x_1410_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1459_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_v_1426_; lean_object* v___x_1427_; lean_object* v_xs_x27_1428_; lean_object* v___y_1430_; 
v_v_1426_ = lean_array_fget(v_es_1415_, v_j_1420_);
v___x_1427_ = lean_box(0);
v_xs_x27_1428_ = lean_array_fset(v_es_1415_, v_j_1420_, v___x_1427_);
switch(lean_obj_tag(v_v_1426_))
{
case 0:
{
lean_object* v_key_1435_; lean_object* v_val_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1446_; 
v_key_1435_ = lean_ctor_get(v_v_1426_, 0);
v_val_1436_ = lean_ctor_get(v_v_1426_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_v_1426_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1438_ = v_v_1426_;
v_isShared_1439_ = v_isSharedCheck_1446_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_val_1436_);
lean_inc(v_key_1435_);
lean_dec(v_v_1426_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1446_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
uint8_t v___x_1440_; 
v___x_1440_ = l_Lean_instBEqMVarId_beq(v_x_1413_, v_key_1435_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_del_object(v___x_1438_);
v___x_1441_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1435_, v_val_1436_, v_x_1413_, v_x_1414_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___y_1430_ = v___x_1442_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1444_; 
lean_dec(v_val_1436_);
lean_dec(v_key_1435_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 1, v_x_1414_);
lean_ctor_set(v___x_1438_, 0, v_x_1413_);
v___x_1444_ = v___x_1438_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_x_1413_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_x_1414_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v___y_1430_ = v___x_1444_;
goto v___jp_1429_;
}
}
}
}
case 1:
{
lean_object* v_node_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1457_; 
v_node_1447_ = lean_ctor_get(v_v_1426_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_v_1426_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1449_ = v_v_1426_;
v_isShared_1450_ = v_isSharedCheck_1457_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_node_1447_);
lean_dec(v_v_1426_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1457_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1451_ = lean_usize_shift_right(v_x_1411_, v___x_1416_);
v___x_1452_ = lean_usize_add(v_x_1412_, v___x_1417_);
v___x_1453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1447_, v___x_1451_, v___x_1452_, v_x_1413_, v_x_1414_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1453_);
v___x_1455_ = v___x_1449_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
v___y_1430_ = v___x_1455_;
goto v___jp_1429_;
}
}
}
default: 
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_x_1413_);
lean_ctor_set(v___x_1458_, 1, v_x_1414_);
v___y_1430_ = v___x_1458_;
goto v___jp_1429_;
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_array_fset(v_xs_x27_1428_, v_j_1420_, v___y_1430_);
lean_dec(v_j_1420_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1431_);
v___x_1433_ = v___x_1424_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v_ks_1461_; lean_object* v_vs_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1482_; 
v_ks_1461_ = lean_ctor_get(v_x_1410_, 0);
v_vs_1462_ = lean_ctor_get(v_x_1410_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1464_ = v_x_1410_;
v_isShared_1465_ = v_isSharedCheck_1482_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_vs_1462_);
lean_inc(v_ks_1461_);
lean_dec(v_x_1410_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1482_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_ks_1461_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_vs_1462_);
v___x_1467_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v_newNode_1468_; uint8_t v___y_1470_; size_t v___x_1476_; uint8_t v___x_1477_; 
v_newNode_1468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1467_, v_x_1413_, v_x_1414_);
v___x_1476_ = ((size_t)7ULL);
v___x_1477_ = lean_usize_dec_le(v___x_1476_, v_x_1412_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1478_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1468_);
v___x_1479_ = lean_unsigned_to_nat(4u);
v___x_1480_ = lean_nat_dec_lt(v___x_1478_, v___x_1479_);
lean_dec(v___x_1478_);
v___y_1470_ = v___x_1480_;
goto v___jp_1469_;
}
else
{
v___y_1470_ = v___x_1477_;
goto v___jp_1469_;
}
v___jp_1469_:
{
if (v___y_1470_ == 0)
{
lean_object* v_ks_1471_; lean_object* v_vs_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_ks_1471_ = lean_ctor_get(v_newNode_1468_, 0);
lean_inc_ref(v_ks_1471_);
v_vs_1472_ = lean_ctor_get(v_newNode_1468_, 1);
lean_inc_ref(v_vs_1472_);
lean_dec_ref(v_newNode_1468_);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1412_, v_ks_1471_, v_vs_1472_, v___x_1473_, v___x_1474_);
lean_dec_ref(v_vs_1472_);
lean_dec_ref(v_ks_1471_);
return v___x_1475_;
}
else
{
return v_newNode_1468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1483_, lean_object* v_keys_1484_, lean_object* v_vals_1485_, lean_object* v_i_1486_, lean_object* v_entries_1487_){
_start:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_array_get_size(v_keys_1484_);
v___x_1489_ = lean_nat_dec_lt(v_i_1486_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_dec(v_i_1486_);
return v_entries_1487_;
}
else
{
lean_object* v_k_1490_; lean_object* v_v_1491_; uint64_t v___x_1492_; size_t v_h_1493_; size_t v___x_1494_; lean_object* v___x_1495_; size_t v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; size_t v_h_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_k_1490_ = lean_array_fget_borrowed(v_keys_1484_, v_i_1486_);
v_v_1491_ = lean_array_fget_borrowed(v_vals_1485_, v_i_1486_);
v___x_1492_ = l_Lean_instHashableMVarId_hash(v_k_1490_);
v_h_1493_ = lean_uint64_to_usize(v___x_1492_);
v___x_1494_ = ((size_t)5ULL);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_sub(v_depth_1483_, v___x_1496_);
v___x_1498_ = lean_usize_mul(v___x_1494_, v___x_1497_);
v_h_1499_ = lean_usize_shift_right(v_h_1493_, v___x_1498_);
v___x_1500_ = lean_nat_add(v_i_1486_, v___x_1495_);
lean_dec(v_i_1486_);
lean_inc(v_v_1491_);
lean_inc(v_k_1490_);
v___x_1501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1487_, v_h_1499_, v_depth_1483_, v_k_1490_, v_v_1491_);
v_i_1486_ = v___x_1500_;
v_entries_1487_ = v___x_1501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1503_, lean_object* v_keys_1504_, lean_object* v_vals_1505_, lean_object* v_i_1506_, lean_object* v_entries_1507_){
_start:
{
size_t v_depth_boxed_1508_; lean_object* v_res_1509_; 
v_depth_boxed_1508_ = lean_unbox_usize(v_depth_1503_);
lean_dec(v_depth_1503_);
v_res_1509_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1508_, v_keys_1504_, v_vals_1505_, v_i_1506_, v_entries_1507_);
lean_dec_ref(v_vals_1505_);
lean_dec_ref(v_keys_1504_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
size_t v_x_838__boxed_1515_; size_t v_x_839__boxed_1516_; lean_object* v_res_1517_; 
v_x_838__boxed_1515_ = lean_unbox_usize(v_x_1511_);
lean_dec(v_x_1511_);
v_x_839__boxed_1516_ = lean_unbox_usize(v_x_1512_);
lean_dec(v_x_1512_);
v_res_1517_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1510_, v_x_838__boxed_1515_, v_x_839__boxed_1516_, v_x_1513_, v_x_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_){
_start:
{
uint64_t v___x_1521_; size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = l_Lean_instHashableMVarId_hash(v_x_1519_);
v___x_1522_ = lean_uint64_to_usize(v___x_1521_);
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1518_, v___x_1522_, v___x_1523_, v_x_1519_, v_x_1520_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1525_, lean_object* v_val_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; lean_object* v_mctx_1530_; lean_object* v_cache_1531_; lean_object* v_zetaDeltaFVarIds_1532_; lean_object* v_postponed_1533_; lean_object* v_diag_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1562_; 
v___x_1529_ = lean_st_ref_take(v___y_1527_);
v_mctx_1530_ = lean_ctor_get(v___x_1529_, 0);
v_cache_1531_ = lean_ctor_get(v___x_1529_, 1);
v_zetaDeltaFVarIds_1532_ = lean_ctor_get(v___x_1529_, 2);
v_postponed_1533_ = lean_ctor_get(v___x_1529_, 3);
v_diag_1534_ = lean_ctor_get(v___x_1529_, 4);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1536_ = v___x_1529_;
v_isShared_1537_ = v_isSharedCheck_1562_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_diag_1534_);
lean_inc(v_postponed_1533_);
lean_inc(v_zetaDeltaFVarIds_1532_);
lean_inc(v_cache_1531_);
lean_inc(v_mctx_1530_);
lean_dec(v___x_1529_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1562_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_depth_1538_; lean_object* v_levelAssignDepth_1539_; lean_object* v_lmvarCounter_1540_; lean_object* v_mvarCounter_1541_; lean_object* v_lDecls_1542_; lean_object* v_decls_1543_; lean_object* v_userNames_1544_; lean_object* v_lAssignment_1545_; lean_object* v_eAssignment_1546_; lean_object* v_dAssignment_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1561_; 
v_depth_1538_ = lean_ctor_get(v_mctx_1530_, 0);
v_levelAssignDepth_1539_ = lean_ctor_get(v_mctx_1530_, 1);
v_lmvarCounter_1540_ = lean_ctor_get(v_mctx_1530_, 2);
v_mvarCounter_1541_ = lean_ctor_get(v_mctx_1530_, 3);
v_lDecls_1542_ = lean_ctor_get(v_mctx_1530_, 4);
v_decls_1543_ = lean_ctor_get(v_mctx_1530_, 5);
v_userNames_1544_ = lean_ctor_get(v_mctx_1530_, 6);
v_lAssignment_1545_ = lean_ctor_get(v_mctx_1530_, 7);
v_eAssignment_1546_ = lean_ctor_get(v_mctx_1530_, 8);
v_dAssignment_1547_ = lean_ctor_get(v_mctx_1530_, 9);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_mctx_1530_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1549_ = v_mctx_1530_;
v_isShared_1550_ = v_isSharedCheck_1561_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_dAssignment_1547_);
lean_inc(v_eAssignment_1546_);
lean_inc(v_lAssignment_1545_);
lean_inc(v_userNames_1544_);
lean_inc(v_decls_1543_);
lean_inc(v_lDecls_1542_);
lean_inc(v_mvarCounter_1541_);
lean_inc(v_lmvarCounter_1540_);
lean_inc(v_levelAssignDepth_1539_);
lean_inc(v_depth_1538_);
lean_dec(v_mctx_1530_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1561_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1546_, v_mvarId_1525_, v_val_1526_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 8, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_depth_1538_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_levelAssignDepth_1539_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_lmvarCounter_1540_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v_mvarCounter_1541_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v_lDecls_1542_);
lean_ctor_set(v_reuseFailAlloc_1560_, 5, v_decls_1543_);
lean_ctor_set(v_reuseFailAlloc_1560_, 6, v_userNames_1544_);
lean_ctor_set(v_reuseFailAlloc_1560_, 7, v_lAssignment_1545_);
lean_ctor_set(v_reuseFailAlloc_1560_, 8, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1560_, 9, v_dAssignment_1547_);
v___x_1553_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1555_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1553_);
v___x_1555_ = v___x_1536_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_cache_1531_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_zetaDeltaFVarIds_1532_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_postponed_1533_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_diag_1534_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_st_ref_set(v___y_1527_, v___x_1555_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1563_, lean_object* v_val_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1563_, v_val_1564_, v___y_1565_);
lean_dec(v___y_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
lean_inc(v_g_1568_);
v___x_1574_ = l_Lean_MVarId_getType(v_g_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = lean_box(0);
v___x_1577_ = l_Lean_Meta_synthInstance(v_a_1575_, v___x_1576_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1587_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1568_, v_a_1578_, v___y_1570_);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v___x_1579_, 0);
lean_dec(v_unused_1588_);
v___x_1581_ = v___x_1579_;
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
else
{
lean_dec(v___x_1579_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_box(0);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_g_1568_);
v_a_1589_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1577_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1577_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_g_1568_);
v_a_1597_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1574_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1574_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1613_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; 
v___f_1614_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1615_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1613_, v___f_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1616_, lean_object* v_val_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1616_, v_val_1617_, v___y_1619_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1624_, lean_object* v_val_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1624_, v_val_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1633_, v_x_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1637_, lean_object* v_x_1638_, size_t v_x_1639_, size_t v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1638_, v_x_1639_, v_x_1640_, v_x_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
size_t v_x_1169__boxed_1650_; size_t v_x_1170__boxed_1651_; lean_object* v_res_1652_; 
v_x_1169__boxed_1650_ = lean_unbox_usize(v_x_1646_);
lean_dec(v_x_1646_);
v_x_1170__boxed_1651_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_res_1652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1644_, v_x_1645_, v_x_1169__boxed_1650_, v_x_1170__boxed_1651_, v_x_1648_, v_x_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1653_, lean_object* v_n_1654_, lean_object* v_k_1655_, lean_object* v_v_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1654_, v_k_1655_, v_v_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1658_, size_t v_depth_1659_, lean_object* v_keys_1660_, lean_object* v_vals_1661_, lean_object* v_heq_1662_, lean_object* v_i_1663_, lean_object* v_entries_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1659_, v_keys_1660_, v_vals_1661_, v_i_1663_, v_entries_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1666_, lean_object* v_depth_1667_, lean_object* v_keys_1668_, lean_object* v_vals_1669_, lean_object* v_heq_1670_, lean_object* v_i_1671_, lean_object* v_entries_1672_){
_start:
{
size_t v_depth_boxed_1673_; lean_object* v_res_1674_; 
v_depth_boxed_1673_ = lean_unbox_usize(v_depth_1667_);
lean_dec(v_depth_1667_);
v_res_1674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1666_, v_depth_boxed_1673_, v_keys_1668_, v_vals_1669_, v_heq_1670_, v_i_1671_, v_entries_1672_);
lean_dec_ref(v_vals_1669_);
lean_dec_ref(v_keys_1668_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1676_, v_x_1677_, v_x_1678_, v_x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1681_, lean_object* v_discharge_1682_, lean_object* v_g_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc(v_g_1683_);
v___x_1689_ = lean_apply_6(v_discharge_1681_, v_g_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec(v_g_1683_);
lean_dec_ref(v_discharge_1682_);
return v___x_1689_;
}
else
{
lean_object* v_a_1690_; uint8_t v___y_1692_; uint8_t v___x_1694_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
v___x_1694_ = l_Lean_Exception_isInterrupt(v_a_1690_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = l_Lean_Exception_isRuntime(v_a_1690_);
v___y_1692_ = v___x_1695_;
goto v___jp_1691_;
}
else
{
lean_dec(v_a_1690_);
v___y_1692_ = v___x_1694_;
goto v___jp_1691_;
}
v___jp_1691_:
{
if (v___y_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_dec_ref(v___x_1689_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1693_ = lean_apply_6(v_discharge_1682_, v_g_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
return v___x_1693_;
}
else
{
lean_dec(v_g_1683_);
lean_dec_ref(v_discharge_1682_);
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1696_, lean_object* v_discharge_1697_, lean_object* v_g_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1696_, v_discharge_1697_, v_g_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1705_, lean_object* v_discharge_1706_){
_start:
{
lean_object* v_toApplyRulesConfig_1707_; lean_object* v_toBacktrackConfig_1708_; uint8_t v_backtracking_1709_; uint8_t v_intro_1710_; uint8_t v_constructor_1711_; uint8_t v_suggestions_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1744_; 
v_toApplyRulesConfig_1707_ = lean_ctor_get(v_cfg_1705_, 0);
lean_inc_ref(v_toApplyRulesConfig_1707_);
v_toBacktrackConfig_1708_ = lean_ctor_get(v_toApplyRulesConfig_1707_, 0);
lean_inc_ref(v_toBacktrackConfig_1708_);
v_backtracking_1709_ = lean_ctor_get_uint8(v_cfg_1705_, sizeof(void*)*1);
v_intro_1710_ = lean_ctor_get_uint8(v_cfg_1705_, sizeof(void*)*1 + 1);
v_constructor_1711_ = lean_ctor_get_uint8(v_cfg_1705_, sizeof(void*)*1 + 2);
v_suggestions_1712_ = lean_ctor_get_uint8(v_cfg_1705_, sizeof(void*)*1 + 3);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_cfg_1705_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_cfg_1705_, 0);
lean_dec(v_unused_1745_);
v___x_1714_ = v_cfg_1705_;
v_isShared_1715_ = v_isSharedCheck_1744_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v_cfg_1705_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1744_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_toApplyConfig_1716_; uint8_t v_transparency_1717_; uint8_t v_symm_1718_; uint8_t v_exfalso_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1742_; 
v_toApplyConfig_1716_ = lean_ctor_get(v_toApplyRulesConfig_1707_, 1);
v_transparency_1717_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1707_, sizeof(void*)*2);
v_symm_1718_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1707_, sizeof(void*)*2 + 1);
v_exfalso_1719_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1707_, sizeof(void*)*2 + 2);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_toApplyRulesConfig_1707_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v_toApplyRulesConfig_1707_, 0);
lean_dec(v_unused_1743_);
v___x_1721_ = v_toApplyRulesConfig_1707_;
v_isShared_1722_ = v_isSharedCheck_1742_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_toApplyConfig_1716_);
lean_dec(v_toApplyRulesConfig_1707_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1742_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_maxDepth_1723_; lean_object* v_proc_1724_; lean_object* v_suspend_1725_; lean_object* v_discharge_1726_; uint8_t v_commitIndependentGoals_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1741_; 
v_maxDepth_1723_ = lean_ctor_get(v_toBacktrackConfig_1708_, 0);
v_proc_1724_ = lean_ctor_get(v_toBacktrackConfig_1708_, 1);
v_suspend_1725_ = lean_ctor_get(v_toBacktrackConfig_1708_, 2);
v_discharge_1726_ = lean_ctor_get(v_toBacktrackConfig_1708_, 3);
v_commitIndependentGoals_1727_ = lean_ctor_get_uint8(v_toBacktrackConfig_1708_, sizeof(void*)*4);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_toBacktrackConfig_1708_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1729_ = v_toBacktrackConfig_1708_;
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_discharge_1726_);
lean_inc(v_suspend_1725_);
lean_inc(v_proc_1724_);
lean_inc(v_maxDepth_1723_);
lean_dec(v_toBacktrackConfig_1708_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___f_1731_; lean_object* v___x_1733_; 
v___f_1731_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1731_, 0, v_discharge_1706_);
lean_closure_set(v___f_1731_, 1, v_discharge_1726_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 3, v___f_1731_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_maxDepth_1723_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_proc_1724_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_suspend_1725_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v___f_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*4, v_commitIndependentGoals_1727_);
v___x_1733_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1733_);
v___x_1735_ = v___x_1721_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_toApplyConfig_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*2, v_transparency_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*2 + 1, v_symm_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*2 + 2, v_exfalso_1719_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1735_);
v___x_1737_ = v___x_1714_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*1, v_backtracking_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*1 + 1, v_intro_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*1 + 2, v_constructor_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1738_, sizeof(void*)*1 + 3, v_suggestions_1712_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = 1;
v___x_1753_ = l_Lean_Meta_intro1Core(v_g_1746_, v___x_1752_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1772_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1772_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1772_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_snd_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1770_; 
v_snd_1758_ = lean_ctor_get(v_a_1754_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v_a_1754_, 0);
lean_dec(v_unused_1771_);
v___x_1760_ = v_a_1754_;
v_isShared_1761_ = v_isSharedCheck_1770_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_snd_1758_);
lean_dec(v_a_1754_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1770_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_box(0);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 1, v___x_1762_);
lean_ctor_set(v___x_1760_, 0, v_snd_1758_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_snd_1758_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1765_);
v___x_1767_ = v___x_1756_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_a_1773_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1753_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1753_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1789_){
_start:
{
lean_object* v___f_1790_; lean_object* v___x_1791_; 
v___f_1790_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1791_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1789_, v___f_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1803_ = l_Lean_MVarId_constructor(v_g_1796_, v___x_1802_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1812_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1812_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1804_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1810_ = v___x_1806_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1803_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1803_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1829_){
_start:
{
lean_object* v___f_1830_; lean_object* v___x_1831_; 
v___f_1830_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1831_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1829_, v___f_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; 
lean_inc(v_g_1834_);
v___x_1840_ = l_Lean_MVarId_getType(v_g_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = lean_box(0);
v___x_1843_ = l_Lean_Meta_synthInstance(v_a_1841_, v___x_1842_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1853_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1834_, v_a_1844_, v___y_1836_);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v___x_1845_, 0);
lean_dec(v_unused_1854_);
v___x_1847_ = v___x_1845_;
v_isShared_1848_ = v_isSharedCheck_1853_;
goto v_resetjp_1846_;
}
else
{
lean_dec(v___x_1845_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1853_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_g_1834_);
v_a_1855_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1843_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1843_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_g_1834_);
v_a_1863_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1840_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1840_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1879_){
_start:
{
lean_object* v___f_1880_; lean_object* v___x_1881_; 
v___f_1880_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1881_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1879_, v___f_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1882_, lean_object* v___y_1883_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = l_Lean_Expr_hasMVar(v_e_1882_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v_e_1882_);
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; lean_object* v_mctx_1888_; lean_object* v___x_1889_; lean_object* v_fst_1890_; lean_object* v_snd_1891_; lean_object* v___x_1892_; lean_object* v_cache_1893_; lean_object* v_zetaDeltaFVarIds_1894_; lean_object* v_postponed_1895_; lean_object* v_diag_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1905_; 
v___x_1887_ = lean_st_ref_get(v___y_1883_);
v_mctx_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_mctx_1888_);
lean_dec(v___x_1887_);
v___x_1889_ = l_Lean_instantiateMVarsCore(v_mctx_1888_, v_e_1882_);
v_fst_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_fst_1890_);
v_snd_1891_ = lean_ctor_get(v___x_1889_, 1);
lean_inc(v_snd_1891_);
lean_dec_ref(v___x_1889_);
v___x_1892_ = lean_st_ref_take(v___y_1883_);
v_cache_1893_ = lean_ctor_get(v___x_1892_, 1);
v_zetaDeltaFVarIds_1894_ = lean_ctor_get(v___x_1892_, 2);
v_postponed_1895_ = lean_ctor_get(v___x_1892_, 3);
v_diag_1896_ = lean_ctor_get(v___x_1892_, 4);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1906_);
v___x_1898_ = v___x_1892_;
v_isShared_1899_ = v_isSharedCheck_1905_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_diag_1896_);
lean_inc(v_postponed_1895_);
lean_inc(v_zetaDeltaFVarIds_1894_);
lean_inc(v_cache_1893_);
lean_dec(v___x_1892_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1905_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v_snd_1891_);
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_snd_1891_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_cache_1893_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_zetaDeltaFVarIds_1894_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v_postponed_1895_);
lean_ctor_set(v_reuseFailAlloc_1904_, 4, v_diag_1896_);
v___x_1901_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_st_ref_set(v___y_1883_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_fst_1890_);
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1907_, v___y_1908_);
lean_dec(v___y_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1911_, v___y_1913_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1925_, lean_object* v_x_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1925_, v_x_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1957_, lean_object* v_mvarId_1958_, lean_object* v_x_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1958_, v_x_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_mvarId_1967_, lean_object* v_x_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1966_, v_mvarId_1967_, v_x_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_ref_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1991_; 
v_ref_1981_ = lean_ctor_get(v___y_1978_, 5);
v___x_1982_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_inc(v_ref_1981_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_ref_1981_);
lean_ctor_set(v___x_1987_, 1, v_a_1983_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 1);
lean_ctor_set(v___x_1985_, 0, v___x_1987_);
v___x_1989_ = v___x_1985_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = l_List_reverse___redArg(v_x_2000_);
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
return v___x_2007_;
}
else
{
lean_object* v_head_2008_; lean_object* v_tail_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2029_; 
v_head_2008_ = lean_ctor_get(v_x_1999_, 0);
v_tail_2009_ = lean_ctor_get(v_x_1999_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_x_1999_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2011_ = v_x_1999_;
v_isShared_2012_ = v_isSharedCheck_2029_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_tail_2009_);
lean_inc(v_head_2008_);
lean_dec(v_x_1999_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2029_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_inc(v_head_2008_);
v___x_2013_ = l_Lean_Expr_mvar___override(v_head_2008_);
v___x_2014_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_2014_, 0, v___x_2013_);
v___x_2015_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_2008_, v___x_2014_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v_x_2000_);
lean_ctor_set(v___x_2011_, 0, v_a_2016_);
v___x_2018_ = v___x_2011_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2016_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_x_2000_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
v_x_1999_ = v_tail_2009_;
v_x_2000_ = v___x_2018_;
goto _start;
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_del_object(v___x_2011_);
lean_dec(v_tail_2009_);
lean_dec(v_x_2000_);
v_a_2021_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2015_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2015_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2030_, v_x_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2037_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2041_, lean_object* v_proc_2042_, lean_object* v_orig_2043_, lean_object* v_goals_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_box(0);
lean_inc(v_orig_2043_);
v___x_2051_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2043_, v___x_2050_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
v___x_2053_ = lean_apply_6(v_test_2041_, v_a_2052_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, lean_box(0));
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; uint8_t v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = lean_unbox(v_a_2054_);
lean_dec(v_a_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_goals_2044_);
lean_dec(v_orig_2043_);
lean_dec_ref(v_proc_2042_);
v___x_2056_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2057_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2056_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v___x_2066_; 
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
v___x_2066_ = lean_apply_7(v_proc_2042_, v_orig_2043_, v_goals_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, lean_box(0));
return v___x_2066_;
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_goals_2044_);
lean_dec(v_orig_2043_);
lean_dec_ref(v_proc_2042_);
v_a_2067_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2053_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2053_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_goals_2044_);
lean_dec(v_orig_2043_);
lean_dec_ref(v_proc_2042_);
lean_dec_ref(v_test_2041_);
v_a_2075_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2051_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2051_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2083_, lean_object* v_proc_2084_, lean_object* v_orig_2085_, lean_object* v_goals_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2083_, v_proc_2084_, v_orig_2085_, v_goals_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2093_, lean_object* v_test_2094_){
_start:
{
lean_object* v_toApplyRulesConfig_2095_; lean_object* v_toBacktrackConfig_2096_; uint8_t v_backtracking_2097_; uint8_t v_intro_2098_; uint8_t v_constructor_2099_; uint8_t v_suggestions_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2132_; 
v_toApplyRulesConfig_2095_ = lean_ctor_get(v_cfg_2093_, 0);
lean_inc_ref(v_toApplyRulesConfig_2095_);
v_toBacktrackConfig_2096_ = lean_ctor_get(v_toApplyRulesConfig_2095_, 0);
lean_inc_ref(v_toBacktrackConfig_2096_);
v_backtracking_2097_ = lean_ctor_get_uint8(v_cfg_2093_, sizeof(void*)*1);
v_intro_2098_ = lean_ctor_get_uint8(v_cfg_2093_, sizeof(void*)*1 + 1);
v_constructor_2099_ = lean_ctor_get_uint8(v_cfg_2093_, sizeof(void*)*1 + 2);
v_suggestions_2100_ = lean_ctor_get_uint8(v_cfg_2093_, sizeof(void*)*1 + 3);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_cfg_2093_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v_cfg_2093_, 0);
lean_dec(v_unused_2133_);
v___x_2102_ = v_cfg_2093_;
v_isShared_2103_ = v_isSharedCheck_2132_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_cfg_2093_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2132_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_toApplyConfig_2104_; uint8_t v_transparency_2105_; uint8_t v_symm_2106_; uint8_t v_exfalso_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2130_; 
v_toApplyConfig_2104_ = lean_ctor_get(v_toApplyRulesConfig_2095_, 1);
v_transparency_2105_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2095_, sizeof(void*)*2);
v_symm_2106_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2095_, sizeof(void*)*2 + 1);
v_exfalso_2107_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2095_, sizeof(void*)*2 + 2);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_toApplyRulesConfig_2095_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_toApplyRulesConfig_2095_, 0);
lean_dec(v_unused_2131_);
v___x_2109_ = v_toApplyRulesConfig_2095_;
v_isShared_2110_ = v_isSharedCheck_2130_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_toApplyConfig_2104_);
lean_dec(v_toApplyRulesConfig_2095_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2130_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_maxDepth_2111_; lean_object* v_proc_2112_; lean_object* v_suspend_2113_; lean_object* v_discharge_2114_; uint8_t v_commitIndependentGoals_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2129_; 
v_maxDepth_2111_ = lean_ctor_get(v_toBacktrackConfig_2096_, 0);
v_proc_2112_ = lean_ctor_get(v_toBacktrackConfig_2096_, 1);
v_suspend_2113_ = lean_ctor_get(v_toBacktrackConfig_2096_, 2);
v_discharge_2114_ = lean_ctor_get(v_toBacktrackConfig_2096_, 3);
v_commitIndependentGoals_2115_ = lean_ctor_get_uint8(v_toBacktrackConfig_2096_, sizeof(void*)*4);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_toBacktrackConfig_2096_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2117_ = v_toBacktrackConfig_2096_;
v_isShared_2118_ = v_isSharedCheck_2129_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_discharge_2114_);
lean_inc(v_suspend_2113_);
lean_inc(v_proc_2112_);
lean_inc(v_maxDepth_2111_);
lean_dec(v_toBacktrackConfig_2096_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2129_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___f_2119_; lean_object* v___x_2121_; 
v___f_2119_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2119_, 0, v_test_2094_);
lean_closure_set(v___f_2119_, 1, v_proc_2112_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v___f_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_maxDepth_2111_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___f_2119_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_suspend_2113_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_discharge_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2128_, sizeof(void*)*4, v_commitIndependentGoals_2115_);
v___x_2121_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2121_);
v___x_2123_ = v___x_2109_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_toApplyConfig_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*2, v_transparency_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*2 + 1, v_symm_2106_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*2 + 2, v_exfalso_2107_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2123_);
v___x_2125_ = v___x_2102_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2126_, sizeof(void*)*1, v_backtracking_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2126_, sizeof(void*)*1 + 1, v_intro_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2126_, sizeof(void*)*1 + 2, v_constructor_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2126_, sizeof(void*)*1 + 3, v_suggestions_2100_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2134_, lean_object* v_msg_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_msg_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2142_, v_msg_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2151_, lean_object* v_sols_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0));
lean_inc(v_sols_2152_);
v___x_2159_ = l_List_any___redArg(v_sols_2152_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_inc(v___y_2156_);
lean_inc_ref(v___y_2155_);
lean_inc(v___y_2154_);
lean_inc_ref(v___y_2153_);
v___x_2160_ = lean_apply_6(v_test_2151_, v_sols_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, lean_box(0));
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec(v_sols_2152_);
lean_dec_ref(v_test_2151_);
v___x_2161_ = lean_box(v___x_2159_);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2163_, lean_object* v_sols_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2163_, v_sols_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2171_, lean_object* v_test_2172_){
_start:
{
lean_object* v___f_2173_; lean_object* v___x_2174_; 
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2173_, 0, v_test_2172_);
v___x_2174_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2171_, v___f_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_e_2175_, lean_object* v_s_2176_){
_start:
{
uint8_t v___x_2177_; 
v___x_2177_ = l_Lean_Expr_occurs(v_e_2175_, v_s_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_e_2178_, lean_object* v_s_2179_){
_start:
{
uint8_t v_res_2180_; lean_object* v_r_2181_; 
v_res_2180_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_e_2178_, v_s_2179_);
lean_dec_ref(v_s_2179_);
v_r_2181_ = lean_box(v_res_2180_);
return v_r_2181_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object* v_sols_2182_, lean_object* v_e_2183_){
_start:
{
lean_object* v___f_2184_; uint8_t v___x_2185_; 
v___f_2184_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2184_, 0, v_e_2183_);
v___x_2185_ = l_List_any___redArg(v_sols_2182_, v___f_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object* v_sols_2186_, lean_object* v_e_2187_){
_start:
{
uint8_t v_res_2188_; lean_object* v_r_2189_; 
v_res_2188_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(v_sols_2186_, v_e_2187_);
v_r_2189_ = lean_box(v_res_2188_);
return v_r_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object* v_use_2190_, lean_object* v_sols_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___f_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2197_, 0, v_sols_2191_);
v___x_2198_ = l_List_all___redArg(v_use_2190_, v___f_2197_);
v___x_2199_ = lean_box(v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object* v_use_2201_, lean_object* v_sols_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(v_use_2201_, v_sols_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2209_, lean_object* v_use_2210_){
_start:
{
lean_object* v___f_2211_; lean_object* v___x_2212_; 
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2211_, 0, v_use_2210_);
v___x_2212_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2209_, v___f_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2213_){
_start:
{
lean_object* v___y_2215_; lean_object* v_toApplyRulesConfig_2216_; uint8_t v_backtracking_2217_; uint8_t v_intro_2218_; uint8_t v_constructor_2219_; uint8_t v_suggestions_2220_; uint8_t v_intro_2224_; 
v_intro_2224_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1 + 1);
if (v_intro_2224_ == 0)
{
lean_object* v_toApplyRulesConfig_2225_; uint8_t v_backtracking_2226_; uint8_t v_constructor_2227_; uint8_t v_suggestions_2228_; 
v_toApplyRulesConfig_2225_ = lean_ctor_get(v_cfg_2213_, 0);
lean_inc_ref(v_toApplyRulesConfig_2225_);
v_backtracking_2226_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1);
v_constructor_2227_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1 + 2);
v_suggestions_2228_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1 + 3);
v___y_2215_ = v_cfg_2213_;
v_toApplyRulesConfig_2216_ = v_toApplyRulesConfig_2225_;
v_backtracking_2217_ = v_backtracking_2226_;
v_intro_2218_ = v_intro_2224_;
v_constructor_2219_ = v_constructor_2227_;
v_suggestions_2220_ = v_suggestions_2228_;
goto v___jp_2214_;
}
else
{
lean_object* v_toApplyRulesConfig_2229_; uint8_t v_backtracking_2230_; uint8_t v_constructor_2231_; uint8_t v_suggestions_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2246_; 
v_toApplyRulesConfig_2229_ = lean_ctor_get(v_cfg_2213_, 0);
v_backtracking_2230_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1);
v_constructor_2231_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1 + 2);
v_suggestions_2232_ = lean_ctor_get_uint8(v_cfg_2213_, sizeof(void*)*1 + 3);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_cfg_2213_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2234_ = v_cfg_2213_;
v_isShared_2235_ = v_isSharedCheck_2246_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_toApplyRulesConfig_2229_);
lean_dec(v_cfg_2213_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2246_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
uint8_t v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = 0;
if (v_isShared_2235_ == 0)
{
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_toApplyRulesConfig_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*1, v_backtracking_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*1 + 2, v_constructor_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*1 + 3, v_suggestions_2232_);
v___x_2238_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v_toApplyRulesConfig_2240_; uint8_t v_backtracking_2241_; uint8_t v_intro_2242_; uint8_t v_constructor_2243_; uint8_t v_suggestions_2244_; 
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1 + 1, v___x_2236_);
v___x_2239_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2238_);
v_toApplyRulesConfig_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc_ref(v_toApplyRulesConfig_2240_);
v_backtracking_2241_ = lean_ctor_get_uint8(v___x_2239_, sizeof(void*)*1);
v_intro_2242_ = lean_ctor_get_uint8(v___x_2239_, sizeof(void*)*1 + 1);
v_constructor_2243_ = lean_ctor_get_uint8(v___x_2239_, sizeof(void*)*1 + 2);
v_suggestions_2244_ = lean_ctor_get_uint8(v___x_2239_, sizeof(void*)*1 + 3);
v___y_2215_ = v___x_2239_;
v_toApplyRulesConfig_2216_ = v_toApplyRulesConfig_2240_;
v_backtracking_2217_ = v_backtracking_2241_;
v_intro_2218_ = v_intro_2242_;
v_constructor_2219_ = v_constructor_2243_;
v_suggestions_2220_ = v_suggestions_2244_;
goto v___jp_2214_;
}
}
}
v___jp_2214_:
{
if (v_constructor_2219_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2216_);
return v___y_2215_;
}
else
{
uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v___y_2215_);
v___x_2221_ = 0;
v___x_2222_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2222_, 0, v_toApplyRulesConfig_2216_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v_backtracking_2217_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1 + 1, v_intro_2218_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1 + 2, v___x_2221_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1 + 3, v_suggestions_2220_);
v___x_2223_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2222_);
return v___x_2223_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2247_, lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
if (lean_obj_tag(v_x_2247_) == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = l_List_reverse___redArg(v_x_2248_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
else
{
lean_object* v_head_2258_; lean_object* v_tail_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2277_; 
v_head_2258_ = lean_ctor_get(v_x_2247_, 0);
v_tail_2259_ = lean_ctor_get(v_x_2247_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_x_2247_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2261_ = v_x_2247_;
v_isShared_2262_ = v_isSharedCheck_2277_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_tail_2259_);
lean_inc(v_head_2258_);
lean_dec(v_x_2247_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2277_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; 
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc(v___y_2252_);
lean_inc_ref(v___y_2251_);
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
v___x_2263_ = lean_apply_7(v_head_2258_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, lean_box(0));
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v_x_2248_);
lean_ctor_set(v___x_2261_, 0, v_a_2264_);
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2264_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_x_2248_);
v___x_2266_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
v_x_2247_ = v_tail_2259_;
v_x_2248_ = v___x_2266_;
goto _start;
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_del_object(v___x_2261_);
lean_dec(v_tail_2259_);
lean_dec(v_x_2248_);
v_a_2269_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2263_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2263_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2278_, lean_object* v_x_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2278_, v_x_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2288_, lean_object* v_cfg_2289_, lean_object* v_lemmas_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
v___x_2298_ = lean_apply_8(v_ctx_2288_, v_cfg_2289_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, lean_box(0));
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = lean_box(0);
v___x_2301_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2290_, v___x_2300_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2310_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = l_List_appendTR___redArg(v_a_2299_, v_a_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
else
{
lean_dec(v_a_2299_);
return v___x_2301_;
}
}
else
{
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v_lemmas_2290_);
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2311_, lean_object* v_cfg_2312_, lean_object* v_lemmas_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2311_, v_cfg_2312_, v_lemmas_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2322_){
_start:
{
uint8_t v___x_2323_; 
v___x_2323_ = 0;
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2324_);
lean_dec(v_x_2324_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2327_, v___x_2328_, v___x_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2344_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2344_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_fst_2340_; lean_object* v___x_2342_; 
v_fst_2340_ = lean_ctor_get(v_a_2336_, 0);
lean_inc(v_fst_2340_);
lean_dec(v_a_2336_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v_fst_2340_);
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_fst_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
v_a_2345_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2335_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2335_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2353_, lean_object* v___x_2354_, lean_object* v___x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2353_, v___x_2354_, v___x_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2376_, lean_object* v_g_2377_, lean_object* v_lemmas_2378_, lean_object* v_ctx_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___f_2388_; lean_object* v___x_2389_; 
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2385_, 0, v_ctx_2379_);
lean_closure_set(v___f_2385_, 1, v_cfg_2376_);
lean_closure_set(v___f_2385_, 2, v_lemmas_2378_);
v___x_2386_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2387_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2388_, 0, v___f_2385_);
lean_closure_set(v___f_2388_, 1, v___x_2386_);
lean_closure_set(v___f_2388_, 2, v___x_2387_);
v___x_2389_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2377_, v___f_2388_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2390_, lean_object* v_g_2391_, lean_object* v_lemmas_2392_, lean_object* v_ctx_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2390_, v_g_2391_, v_lemmas_2392_, v_ctx_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2400_, lean_object* v_lemmas_2401_, lean_object* v_ctx_2402_, lean_object* v_g_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; 
lean_inc(v_g_2403_);
lean_inc_ref(v_cfg_2400_);
v___x_2409_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2400_, v_g_2403_, v_lemmas_2401_, v_ctx_2402_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_toApplyRulesConfig_2410_; lean_object* v_a_2411_; lean_object* v_toApplyConfig_2412_; uint8_t v_transparency_2413_; lean_object* v___x_2414_; 
v_toApplyRulesConfig_2410_ = lean_ctor_get(v_cfg_2400_, 0);
lean_inc_ref(v_toApplyRulesConfig_2410_);
lean_dec_ref(v_cfg_2400_);
v_a_2411_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2409_);
v_toApplyConfig_2412_ = lean_ctor_get(v_toApplyRulesConfig_2410_, 1);
lean_inc_ref(v_toApplyConfig_2412_);
v_transparency_2413_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2410_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2410_);
v___x_2414_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2412_, v_transparency_2413_, v_a_2411_, v_g_2403_, v_a_2405_, v_a_2407_);
return v___x_2414_;
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_g_2403_);
lean_dec_ref(v_cfg_2400_);
v_a_2415_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2409_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2409_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2423_, lean_object* v_lemmas_2424_, lean_object* v_ctx_2425_, lean_object* v_g_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2423_, v_lemmas_2424_, v_ctx_2425_, v_g_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2433_, lean_object* v_lemmas_2434_, lean_object* v_ctx_2435_, lean_object* v_g_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; 
lean_inc(v_g_2436_);
lean_inc_ref(v_cfg_2433_);
v___x_2442_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2433_, v_g_2436_, v_lemmas_2434_, v_ctx_2435_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_toApplyRulesConfig_2443_; lean_object* v_a_2444_; lean_object* v_toApplyConfig_2445_; uint8_t v_transparency_2446_; lean_object* v___x_2447_; 
v_toApplyRulesConfig_2443_ = lean_ctor_get(v_cfg_2433_, 0);
lean_inc_ref(v_toApplyRulesConfig_2443_);
lean_dec_ref(v_cfg_2433_);
v_a_2444_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2444_);
lean_dec_ref(v___x_2442_);
v_toApplyConfig_2445_ = lean_ctor_get(v_toApplyRulesConfig_2443_, 1);
lean_inc_ref(v_toApplyConfig_2445_);
v_transparency_2446_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2443_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2443_);
v___x_2447_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2445_, v_transparency_2446_, v_a_2444_, v_g_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
return v___x_2447_;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_g_2436_);
lean_dec_ref(v_cfg_2433_);
v_a_2448_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2442_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2442_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2456_, lean_object* v_lemmas_2457_, lean_object* v_ctx_2458_, lean_object* v_g_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2456_, v_lemmas_2457_, v_ctx_2458_, v_g_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
return v_res_2465_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2466_, lean_object* v_i_2467_, lean_object* v_k_2468_){
_start:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = lean_array_get_size(v_keys_2466_);
v___x_2470_ = lean_nat_dec_lt(v_i_2467_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec(v_i_2467_);
return v___x_2470_;
}
else
{
lean_object* v_k_x27_2471_; uint8_t v___x_2472_; 
v_k_x27_2471_ = lean_array_fget_borrowed(v_keys_2466_, v_i_2467_);
v___x_2472_ = l_Lean_instBEqMVarId_beq(v_k_2468_, v_k_x27_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_unsigned_to_nat(1u);
v___x_2474_ = lean_nat_add(v_i_2467_, v___x_2473_);
lean_dec(v_i_2467_);
v_i_2467_ = v___x_2474_;
goto _start;
}
else
{
lean_dec(v_i_2467_);
return v___x_2472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2476_, lean_object* v_i_2477_, lean_object* v_k_2478_){
_start:
{
uint8_t v_res_2479_; lean_object* v_r_2480_; 
v_res_2479_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2476_, v_i_2477_, v_k_2478_);
lean_dec(v_k_2478_);
lean_dec_ref(v_keys_2476_);
v_r_2480_ = lean_box(v_res_2479_);
return v_r_2480_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2481_, size_t v_x_2482_, lean_object* v_x_2483_){
_start:
{
if (lean_obj_tag(v_x_2481_) == 0)
{
lean_object* v_es_2484_; lean_object* v___x_2485_; size_t v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; lean_object* v_j_2489_; lean_object* v___x_2490_; 
v_es_2484_ = lean_ctor_get(v_x_2481_, 0);
v___x_2485_ = lean_box(2);
v___x_2486_ = ((size_t)5ULL);
v___x_2487_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2488_ = lean_usize_land(v_x_2482_, v___x_2487_);
v_j_2489_ = lean_usize_to_nat(v___x_2488_);
v___x_2490_ = lean_array_get_borrowed(v___x_2485_, v_es_2484_, v_j_2489_);
lean_dec(v_j_2489_);
switch(lean_obj_tag(v___x_2490_))
{
case 0:
{
lean_object* v_key_2491_; uint8_t v___x_2492_; 
v_key_2491_ = lean_ctor_get(v___x_2490_, 0);
v___x_2492_ = l_Lean_instBEqMVarId_beq(v_x_2483_, v_key_2491_);
return v___x_2492_;
}
case 1:
{
lean_object* v_node_2493_; size_t v___x_2494_; 
v_node_2493_ = lean_ctor_get(v___x_2490_, 0);
v___x_2494_ = lean_usize_shift_right(v_x_2482_, v___x_2486_);
v_x_2481_ = v_node_2493_;
v_x_2482_ = v___x_2494_;
goto _start;
}
default: 
{
uint8_t v___x_2496_; 
v___x_2496_ = 0;
return v___x_2496_;
}
}
}
else
{
lean_object* v_ks_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v_ks_2497_ = lean_ctor_get(v_x_2481_, 0);
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2497_, v___x_2498_, v_x_2483_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_){
_start:
{
size_t v_x_2218__boxed_2503_; uint8_t v_res_2504_; lean_object* v_r_2505_; 
v_x_2218__boxed_2503_ = lean_unbox_usize(v_x_2501_);
lean_dec(v_x_2501_);
v_res_2504_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2500_, v_x_2218__boxed_2503_, v_x_2502_);
lean_dec(v_x_2502_);
lean_dec_ref(v_x_2500_);
v_r_2505_ = lean_box(v_res_2504_);
return v_r_2505_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
uint64_t v___x_2508_; size_t v___x_2509_; uint8_t v___x_2510_; 
v___x_2508_ = l_Lean_instHashableMVarId_hash(v_x_2507_);
v___x_2509_ = lean_uint64_to_usize(v___x_2508_);
v___x_2510_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2506_, v___x_2509_, v_x_2507_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2511_, lean_object* v_x_2512_){
_start:
{
uint8_t v_res_2513_; lean_object* v_r_2514_; 
v_res_2513_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2511_, v_x_2512_);
lean_dec(v_x_2512_);
lean_dec_ref(v_x_2511_);
v_r_2514_ = lean_box(v_res_2513_);
return v_r_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v_mctx_2519_; lean_object* v_eAssignment_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2518_ = lean_st_ref_get(v___y_2516_);
v_mctx_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_mctx_2519_);
lean_dec(v___x_2518_);
v_eAssignment_2520_ = lean_ctor_get(v_mctx_2519_, 8);
lean_inc_ref(v_eAssignment_2520_);
lean_dec_ref(v_mctx_2519_);
v___x_2521_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2520_, v_mvarId_2515_);
lean_dec_ref(v_eAssignment_2520_);
v___x_2522_ = lean_box(v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec(v_mvarId_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2529_) == 0)
{
return v_x_2528_;
}
else
{
lean_object* v_head_2530_; lean_object* v_tail_2531_; lean_object* v___x_2532_; 
v_head_2530_ = lean_ctor_get(v_x_2529_, 0);
lean_inc(v_head_2530_);
v_tail_2531_ = lean_ctor_get(v_x_2529_, 1);
lean_inc(v_tail_2531_);
lean_dec_ref(v_x_2529_);
v___x_2532_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2528_, v_head_2530_);
v_x_2528_ = v___x_2532_;
v_x_2529_ = v_tail_2531_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2534_, lean_object* v_a_2535_, uint8_t v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
if (lean_obj_tag(v_a_2537_) == 0)
{
if (lean_obj_tag(v_a_2538_) == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v_a_2535_);
lean_dec_ref(v_f_2534_);
v___x_2545_ = lean_box(v_a_2536_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v_a_2539_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
else
{
lean_object* v_head_2548_; lean_object* v_tail_2549_; 
v_head_2548_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_head_2548_);
v_tail_2549_ = lean_ctor_get(v_a_2538_, 1);
lean_inc(v_tail_2549_);
lean_dec_ref(v_a_2538_);
v_a_2537_ = v_head_2548_;
v_a_2538_ = v_tail_2549_;
goto _start;
}
}
else
{
lean_object* v_head_2551_; lean_object* v_tail_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2595_; 
v_head_2551_ = lean_ctor_get(v_a_2537_, 0);
v_tail_2552_ = lean_ctor_get(v_a_2537_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_a_2537_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2554_ = v_a_2537_;
v_isShared_2555_ = v_isSharedCheck_2595_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_tail_2552_);
lean_inc(v_head_2551_);
lean_dec(v_a_2537_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2595_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2594_; 
v___x_2556_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2551_, v___y_2541_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2594_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2594_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
uint8_t v___x_2561_; 
v___x_2561_ = lean_unbox(v_a_2557_);
lean_dec(v_a_2557_);
if (v___x_2561_ == 0)
{
lean_object* v_zero_2562_; uint8_t v_isZero_2563_; 
v_zero_2562_ = lean_unsigned_to_nat(0u);
v_isZero_2563_ = lean_nat_dec_eq(v_a_2535_, v_zero_2562_);
if (v_isZero_2563_ == 1)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
lean_del_object(v___x_2554_);
lean_dec(v_a_2535_);
lean_dec_ref(v_f_2534_);
v___x_2564_ = lean_array_push(v_a_2539_, v_head_2551_);
v___x_2565_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2564_, v_tail_2552_);
v___x_2566_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2565_, v_a_2538_);
v___x_2567_ = lean_box(v_a_2536_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2566_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2568_);
v___x_2570_ = v___x_2559_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_del_object(v___x_2559_);
lean_inc_ref(v_f_2534_);
lean_inc(v_head_2551_);
v___x_2572_ = lean_apply_1(v_f_2534_, v_head_2551_);
v___x_2573_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2572_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v_one_2575_; lean_object* v_n_2576_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref(v___x_2573_);
v_one_2575_ = lean_unsigned_to_nat(1u);
v_n_2576_ = lean_nat_sub(v_a_2535_, v_one_2575_);
lean_dec(v_a_2535_);
if (lean_obj_tag(v_a_2574_) == 0)
{
lean_object* v___x_2577_; 
lean_del_object(v___x_2554_);
v___x_2577_ = lean_array_push(v_a_2539_, v_head_2551_);
v_a_2535_ = v_n_2576_;
v_a_2537_ = v_tail_2552_;
v_a_2539_ = v___x_2577_;
goto _start;
}
else
{
lean_object* v_val_2579_; uint8_t v___x_2580_; lean_object* v___x_2582_; 
lean_dec(v_head_2551_);
v_val_2579_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_val_2579_);
lean_dec_ref(v_a_2574_);
v___x_2580_ = 1;
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 1, v_a_2538_);
lean_ctor_set(v___x_2554_, 0, v_tail_2552_);
v___x_2582_ = v___x_2554_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_tail_2552_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_a_2538_);
v___x_2582_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
v_a_2535_ = v_n_2576_;
v_a_2536_ = v___x_2580_;
v_a_2537_ = v_val_2579_;
v_a_2538_ = v___x_2582_;
goto _start;
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_del_object(v___x_2554_);
lean_dec(v_tail_2552_);
lean_dec(v_head_2551_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec(v_a_2535_);
lean_dec_ref(v_f_2534_);
v_a_2585_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2573_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2573_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
else
{
lean_del_object(v___x_2559_);
lean_del_object(v___x_2554_);
lean_dec(v_head_2551_);
v_a_2537_ = v_tail_2552_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v_a_2299__boxed_2607_; lean_object* v_res_2608_; 
v_a_2299__boxed_2607_ = lean_unbox(v_a_2598_);
v_res_2608_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2596_, v_a_2597_, v_a_2299__boxed_2607_, v_a_2599_, v_a_2600_, v_a_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2609_, size_t v_i_2610_, size_t v_stop_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_a_2619_; uint8_t v___x_2623_; 
v___x_2623_ = lean_usize_dec_eq(v_i_2610_, v_stop_2611_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2627_; 
v___x_2624_ = lean_array_uget_borrowed(v_as_2609_, v_i_2610_);
v___x_2627_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2624_, v___y_2614_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; uint8_t v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = lean_unbox(v_a_2628_);
lean_dec(v_a_2628_);
if (v___x_2629_ == 0)
{
goto v___jp_2625_;
}
else
{
v_a_2619_ = v_b_2612_;
goto v___jp_2618_;
}
}
else
{
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2630_; uint8_t v___x_2631_; 
v_a_2630_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2627_);
v___x_2631_ = lean_unbox(v_a_2630_);
lean_dec(v_a_2630_);
if (v___x_2631_ == 0)
{
v_a_2619_ = v_b_2612_;
goto v___jp_2618_;
}
else
{
goto v___jp_2625_;
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_b_2612_);
v_a_2632_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2627_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2627_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
v___jp_2625_:
{
lean_object* v___x_2626_; 
lean_inc(v___x_2624_);
v___x_2626_ = lean_array_push(v_b_2612_, v___x_2624_);
v_a_2619_ = v___x_2626_;
goto v___jp_2618_;
}
}
else
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_b_2612_);
return v___x_2640_;
}
v___jp_2618_:
{
size_t v___x_2620_; size_t v___x_2621_; 
v___x_2620_ = ((size_t)1ULL);
v___x_2621_ = lean_usize_add(v_i_2610_, v___x_2620_);
v_i_2610_ = v___x_2621_;
v_b_2612_ = v_a_2619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2641_, lean_object* v_i_2642_, lean_object* v_stop_2643_, lean_object* v_b_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
size_t v_i_boxed_2650_; size_t v_stop_boxed_2651_; lean_object* v_res_2652_; 
v_i_boxed_2650_ = lean_unbox_usize(v_i_2642_);
lean_dec(v_i_2642_);
v_stop_boxed_2651_ = lean_unbox_usize(v_stop_2643_);
lean_dec(v_stop_2643_);
v_res_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2641_, v_i_boxed_2650_, v_stop_boxed_2651_, v_b_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec_ref(v_as_2641_);
return v_res_2652_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2656_ = lean_array_to_list(v___x_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2657_, lean_object* v_goals_2658_, lean_object* v_maxIters_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2665_ = 0;
v___x_2666_ = lean_box(0);
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2669_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2657_, v_maxIters_2659_, v___x_2665_, v_goals_2658_, v___x_2666_, v___x_2668_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2719_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2719_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2719_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_fst_2674_; lean_object* v_snd_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2718_; 
v_fst_2674_ = lean_ctor_get(v_a_2670_, 0);
v_snd_2675_ = lean_ctor_get(v_a_2670_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_a_2670_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2677_ = v_a_2670_;
v_isShared_2678_ = v_isSharedCheck_2718_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_snd_2675_);
lean_inc(v_fst_2674_);
lean_dec(v_a_2670_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2718_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_____do__lift_2680_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = lean_array_get_size(v_snd_2675_);
v___x_2689_ = lean_nat_dec_lt(v___x_2667_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_del_object(v___x_2677_);
lean_dec(v_snd_2675_);
lean_del_object(v___x_2672_);
v___x_2690_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_fst_2674_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
return v___x_2692_;
}
else
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_nat_dec_le(v___x_2688_, v___x_2688_);
if (v___x_2693_ == 0)
{
if (v___x_2689_ == 0)
{
lean_dec(v_snd_2675_);
v_____do__lift_2680_ = v___x_2668_;
goto v___jp_2679_;
}
else
{
size_t v___x_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = ((size_t)0ULL);
v___x_2695_ = lean_usize_of_nat(v___x_2688_);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2675_, v___x_2694_, v___x_2695_, v___x_2668_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v_snd_2675_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v_____do__lift_2680_ = v_a_2697_;
goto v___jp_2679_;
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_del_object(v___x_2677_);
lean_dec(v_fst_2674_);
lean_del_object(v___x_2672_);
v_a_2698_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2696_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2696_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
else
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = lean_usize_of_nat(v___x_2688_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2675_, v___x_2706_, v___x_2707_, v___x_2668_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v_snd_2675_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref(v___x_2708_);
v_____do__lift_2680_ = v_a_2709_;
goto v___jp_2679_;
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_del_object(v___x_2677_);
lean_dec(v_fst_2674_);
lean_del_object(v___x_2672_);
v_a_2710_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2708_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2708_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
v___jp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = lean_array_to_list(v_____do__lift_2680_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v___x_2681_);
v___x_2683_ = v___x_2677_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_fst_2674_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2683_);
v___x_2685_ = v___x_2672_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_a_2720_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2669_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2669_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2728_, lean_object* v_goals_2729_, lean_object* v_maxIters_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2728_, v_goals_2729_, v_maxIters_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2736_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2740_, lean_object* v_goals_2741_, lean_object* v_maxIters_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2740_, v_goals_2741_, v_maxIters_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2761_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2761_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2761_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_fst_2753_; uint8_t v___x_2754_; 
v_fst_2753_ = lean_ctor_get(v_a_2749_, 0);
v___x_2754_ = lean_unbox(v_fst_2753_);
if (v___x_2754_ == 1)
{
lean_object* v_snd_2755_; lean_object* v___x_2757_; 
v_snd_2755_ = lean_ctor_get(v_a_2749_, 1);
lean_inc(v_snd_2755_);
lean_dec(v_a_2749_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v_snd_2755_);
v___x_2757_ = v___x_2751_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_snd_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_del_object(v___x_2751_);
lean_dec(v_a_2749_);
v___x_2759_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2760_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2759_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2748_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2748_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2770_, lean_object* v_goals_2771_, lean_object* v_maxIters_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2770_, v_goals_2771_, v_maxIters_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2779_, lean_object* v_ctx_2780_, lean_object* v_cfg_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
uint8_t v_backtracking_2788_; 
v_backtracking_2788_ = lean_ctor_get_uint8(v_cfg_2781_, sizeof(void*)*1);
if (v_backtracking_2788_ == 0)
{
lean_object* v_toApplyRulesConfig_2789_; lean_object* v_toBacktrackConfig_2790_; lean_object* v_maxDepth_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_toApplyRulesConfig_2789_ = lean_ctor_get(v_cfg_2781_, 0);
v_toBacktrackConfig_2790_ = lean_ctor_get(v_toApplyRulesConfig_2789_, 0);
v_maxDepth_2791_ = lean_ctor_get(v_toBacktrackConfig_2790_, 0);
lean_inc(v_maxDepth_2791_);
v___x_2792_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2792_, 0, v_cfg_2781_);
lean_closure_set(v___x_2792_, 1, v_lemmas_2779_);
lean_closure_set(v___x_2792_, 2, v_ctx_2780_);
v___x_2793_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2792_, v_a_2782_, v_maxDepth_2791_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2793_;
}
else
{
lean_object* v_toApplyRulesConfig_2794_; lean_object* v_toBacktrackConfig_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_toApplyRulesConfig_2794_ = lean_ctor_get(v_cfg_2781_, 0);
v_toBacktrackConfig_2795_ = lean_ctor_get(v_toApplyRulesConfig_2794_, 0);
lean_inc_ref(v_toBacktrackConfig_2795_);
v___x_2796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2797_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2797_, 0, v_cfg_2781_);
lean_closure_set(v___x_2797_, 1, v_lemmas_2779_);
lean_closure_set(v___x_2797_, 2, v_ctx_2780_);
v___x_2798_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2795_, v___x_2796_, v___x_2797_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
return v___x_2798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2799_, lean_object* v_ctx_2800_, lean_object* v_cfg_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2799_, v_ctx_2800_, v_cfg_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2809_, v___y_2811_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v_mvarId_2816_);
return v_res_2822_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_){
_start:
{
uint8_t v___x_2826_; 
v___x_2826_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2824_, v_x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_){
_start:
{
uint8_t v_res_2830_; lean_object* v_r_2831_; 
v_res_2830_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2827_, v_x_2828_, v_x_2829_);
lean_dec(v_x_2829_);
lean_dec_ref(v_x_2828_);
v_r_2831_ = lean_box(v_res_2830_);
return v_r_2831_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2832_, lean_object* v_x_2833_, size_t v_x_2834_, lean_object* v_x_2835_){
_start:
{
uint8_t v___x_2836_; 
v___x_2836_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2833_, v_x_2834_, v_x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2837_, lean_object* v_x_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_){
_start:
{
size_t v_x_2759__boxed_2841_; uint8_t v_res_2842_; lean_object* v_r_2843_; 
v_x_2759__boxed_2841_ = lean_unbox_usize(v_x_2839_);
lean_dec(v_x_2839_);
v_res_2842_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2837_, v_x_2838_, v_x_2759__boxed_2841_, v_x_2840_);
lean_dec(v_x_2840_);
lean_dec_ref(v_x_2838_);
v_r_2843_ = lean_box(v_res_2842_);
return v_r_2843_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2844_, lean_object* v_keys_2845_, lean_object* v_vals_2846_, lean_object* v_heq_2847_, lean_object* v_i_2848_, lean_object* v_k_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2845_, v_i_2848_, v_k_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2851_, lean_object* v_keys_2852_, lean_object* v_vals_2853_, lean_object* v_heq_2854_, lean_object* v_i_2855_, lean_object* v_k_2856_){
_start:
{
uint8_t v_res_2857_; lean_object* v_r_2858_; 
v_res_2857_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2851_, v_keys_2852_, v_vals_2853_, v_heq_2854_, v_i_2855_, v_k_2856_);
lean_dec(v_k_2856_);
lean_dec_ref(v_vals_2853_);
lean_dec_ref(v_keys_2852_);
v_r_2858_ = lean_box(v_res_2857_);
return v_r_2858_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2861_ = l_Lean_stringToMessageData(v___x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_x_2870_);
return v_res_2876_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2879_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2880_ = l_Lean_Name_append(v___x_2879_, v___x_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2881_, lean_object* v_lemmas_2882_, lean_object* v_ctx_2883_, lean_object* v_goals_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_cfg_2890_; lean_object* v___x_2891_; 
v_cfg_2890_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2881_);
lean_inc(v_goals_2884_);
lean_inc_ref(v_cfg_2890_);
lean_inc_ref(v_ctx_2883_);
lean_inc(v_lemmas_2882_);
v___x_2891_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v_goals_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_dec_ref(v_cfg_2890_);
lean_dec(v_goals_2884_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
return v___x_2891_;
}
else
{
lean_object* v_a_2892_; lean_object* v___f_2893_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2915_; lean_object* v___y_2916_; uint8_t v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v_a_2922_; lean_object* v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; uint8_t v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v_a_2932_; lean_object* v___y_2942_; uint8_t v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; uint8_t v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v_a_2949_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; uint8_t v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; uint8_t v___y_2994_; uint8_t v___x_3047_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
v___f_2893_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3047_ = l_Lean_Exception_isInterrupt(v_a_2892_);
if (v___x_3047_ == 0)
{
uint8_t v___x_3048_; 
v___x_3048_ = l_Lean_Exception_isRuntime(v_a_2892_);
v___y_2994_ = v___x_3048_;
goto v___jp_2993_;
}
else
{
lean_dec(v_a_2892_);
v___y_2994_ = v___x_3047_;
goto v___jp_2993_;
}
v___jp_2894_:
{
lean_object* v___x_2903_; double v___x_2904_; double v___x_2905_; double v___x_2906_; double v___x_2907_; double v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2903_ = lean_io_mono_nanos_now();
v___x_2904_ = lean_float_of_nat(v___y_2895_);
v___x_2905_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2906_ = lean_float_div(v___x_2904_, v___x_2905_);
v___x_2907_ = lean_float_of_nat(v___x_2903_);
v___x_2908_ = lean_float_div(v___x_2907_, v___x_2905_);
v___x_2909_ = lean_box_float(v___x_2906_);
v___x_2910_ = lean_box_float(v___x_2908_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2902_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
lean_inc_ref(v___y_2900_);
lean_inc(v___y_2901_);
v___x_2913_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2901_, v___y_2899_, v___y_2900_, v___y_2898_, v___y_2897_, v___y_2896_, v___f_2893_, v___x_2912_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_2913_;
}
v___jp_2914_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_a_2922_);
v___y_2895_ = v___y_2915_;
v___y_2896_ = v___y_2916_;
v___y_2897_ = v___y_2917_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2919_;
v___y_2900_ = v___y_2920_;
v___y_2901_ = v___y_2921_;
v_a_2902_ = v___x_2923_;
goto v___jp_2894_;
}
v___jp_2924_:
{
lean_object* v___x_2933_; double v___x_2934_; double v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2933_ = lean_io_get_num_heartbeats();
v___x_2934_ = lean_float_of_nat(v___y_2928_);
v___x_2935_ = lean_float_of_nat(v___x_2933_);
v___x_2936_ = lean_box_float(v___x_2934_);
v___x_2937_ = lean_box_float(v___x_2935_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2932_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
lean_inc_ref(v___y_2930_);
lean_inc(v___y_2931_);
v___x_2940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2931_, v___y_2929_, v___y_2930_, v___y_2927_, v___y_2926_, v___y_2925_, v___f_2893_, v___x_2939_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_2940_;
}
v___jp_2941_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_a_2949_);
v___y_2925_ = v___y_2942_;
v___y_2926_ = v___y_2943_;
v___y_2927_ = v___y_2945_;
v___y_2928_ = v___y_2944_;
v___y_2929_ = v___y_2946_;
v___y_2930_ = v___y_2947_;
v___y_2931_ = v___y_2948_;
v_a_2932_ = v___x_2950_;
goto v___jp_2924_;
}
v___jp_2951_:
{
lean_object* v___x_2959_; lean_object* v_a_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2959_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2888_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2962_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2955_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_io_mono_nanos_now();
v___x_2964_ = l_Lean_MVarId_exfalso(v___y_2953_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2965_);
lean_ctor_set(v___x_2966_, 1, v___y_2952_);
v___x_2967_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v___x_2966_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 1);
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
v___y_2895_ = v___x_2963_;
v___y_2896_ = v_a_2960_;
v___y_2897_ = v___y_2954_;
v___y_2898_ = v___y_2955_;
v___y_2899_ = v___y_2956_;
v___y_2900_ = v___y_2957_;
v___y_2901_ = v___y_2958_;
v_a_2902_ = v___x_2973_;
goto v___jp_2894_;
}
}
}
else
{
lean_object* v_a_2976_; 
v_a_2976_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2976_);
lean_dec_ref(v___x_2967_);
v___y_2915_ = v___x_2963_;
v___y_2916_ = v_a_2960_;
v___y_2917_ = v___y_2954_;
v___y_2918_ = v___y_2955_;
v___y_2919_ = v___y_2956_;
v___y_2920_ = v___y_2957_;
v___y_2921_ = v___y_2958_;
v_a_2922_ = v_a_2976_;
goto v___jp_2914_;
}
}
else
{
lean_object* v_a_2977_; 
lean_dec(v___y_2952_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_2977_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v___x_2964_);
v___y_2915_ = v___x_2963_;
v___y_2916_ = v_a_2960_;
v___y_2917_ = v___y_2954_;
v___y_2918_ = v___y_2955_;
v___y_2919_ = v___y_2956_;
v___y_2920_ = v___y_2957_;
v___y_2921_ = v___y_2958_;
v_a_2922_ = v_a_2977_;
goto v___jp_2914_;
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_io_get_num_heartbeats();
v___x_2979_ = l_Lean_MVarId_exfalso(v___y_2953_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_a_2980_);
lean_ctor_set(v___x_2981_, 1, v___y_2952_);
v___x_2982_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v___x_2981_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 1);
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
v___y_2925_ = v_a_2960_;
v___y_2926_ = v___y_2954_;
v___y_2927_ = v___y_2955_;
v___y_2928_ = v___x_2978_;
v___y_2929_ = v___y_2956_;
v___y_2930_ = v___y_2957_;
v___y_2931_ = v___y_2958_;
v_a_2932_ = v___x_2988_;
goto v___jp_2924_;
}
}
}
else
{
lean_object* v_a_2991_; 
v_a_2991_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2982_);
v___y_2942_ = v_a_2960_;
v___y_2943_ = v___y_2954_;
v___y_2944_ = v___x_2978_;
v___y_2945_ = v___y_2955_;
v___y_2946_ = v___y_2956_;
v___y_2947_ = v___y_2957_;
v___y_2948_ = v___y_2958_;
v_a_2949_ = v_a_2991_;
goto v___jp_2941_;
}
}
else
{
lean_object* v_a_2992_; 
lean_dec(v___y_2952_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_2992_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2979_);
v___y_2942_ = v_a_2960_;
v___y_2943_ = v___y_2954_;
v___y_2944_ = v___x_2978_;
v___y_2945_ = v___y_2955_;
v___y_2946_ = v___y_2956_;
v___y_2947_ = v___y_2957_;
v___y_2948_ = v___y_2958_;
v_a_2949_ = v_a_2992_;
goto v___jp_2941_;
}
}
}
v___jp_2993_:
{
if (v___y_2994_ == 0)
{
if (lean_obj_tag(v_goals_2884_) == 1)
{
lean_object* v_tail_2995_; 
v_tail_2995_ = lean_ctor_get(v_goals_2884_, 1);
lean_inc(v_tail_2995_);
if (lean_obj_tag(v_tail_2995_) == 0)
{
lean_object* v_toApplyRulesConfig_2996_; uint8_t v_exfalso_2997_; 
v_toApplyRulesConfig_2996_ = lean_ctor_get(v_cfg_2890_, 0);
lean_inc_ref(v_toApplyRulesConfig_2996_);
v_exfalso_2997_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2996_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2996_);
if (v_exfalso_2997_ == 1)
{
lean_object* v_options_2998_; uint8_t v_hasTrace_2999_; 
lean_dec_ref(v___x_2891_);
v_options_2998_ = lean_ctor_get(v_a_2887_, 2);
v_hasTrace_2999_ = lean_ctor_get_uint8(v_options_2998_, sizeof(void*)*1);
if (v_hasTrace_2999_ == 0)
{
lean_object* v_head_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3018_; 
v_head_3000_ = lean_ctor_get(v_goals_2884_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_goals_2884_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v_goals_2884_, 1);
lean_dec(v_unused_3019_);
v___x_3002_ = v_goals_2884_;
v_isShared_3003_ = v_isSharedCheck_3018_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_head_3000_);
lean_dec(v_goals_2884_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3018_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_MVarId_exfalso(v_head_3000_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v_a_3005_);
v___x_3007_ = v___x_3002_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3005_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_tail_2995_);
v___x_3007_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v___x_3007_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_3008_;
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_del_object(v___x_3002_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_3010_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3004_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3004_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
else
{
lean_object* v_head_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3045_; 
v_head_3020_ = lean_ctor_get(v_goals_2884_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_goals_2884_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; 
v_unused_3046_ = lean_ctor_get(v_goals_2884_, 1);
lean_dec(v_unused_3046_);
v___x_3022_ = v_goals_2884_;
v_isShared_3023_ = v_isSharedCheck_3045_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_head_3020_);
lean_dec(v_goals_2884_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3045_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_inheritedTraceOptions_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_inheritedTraceOptions_3024_ = lean_ctor_get(v_a_2887_, 13);
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3026_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3027_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3028_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3024_, v_options_2998_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = l_Lean_trace_profiler;
v___x_3030_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2998_, v___x_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_MVarId_exfalso(v_head_3020_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v_a_3032_);
v___x_3034_ = v___x_3022_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3032_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_tail_2995_);
v___x_3034_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2882_, v_ctx_2883_, v_cfg_2890_, v___x_3034_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
return v___x_3035_;
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_del_object(v___x_3022_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
v_a_3037_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3031_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3031_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_del_object(v___x_3022_);
v___y_2952_ = v_tail_2995_;
v___y_2953_ = v_head_3020_;
v___y_2954_ = v___x_3028_;
v___y_2955_ = v_options_2998_;
v___y_2956_ = v_exfalso_2997_;
v___y_2957_ = v___x_3026_;
v___y_2958_ = v___x_3025_;
goto v___jp_2951_;
}
}
else
{
lean_del_object(v___x_3022_);
v___y_2952_ = v_tail_2995_;
v___y_2953_ = v_head_3020_;
v___y_2954_ = v___x_3028_;
v___y_2955_ = v_options_2998_;
v___y_2956_ = v_exfalso_2997_;
v___y_2957_ = v___x_3026_;
v___y_2958_ = v___x_3025_;
goto v___jp_2951_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2884_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
return v___x_2891_;
}
}
else
{
lean_dec(v_tail_2995_);
lean_dec_ref(v_goals_2884_);
lean_dec_ref(v_cfg_2890_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
return v___x_2891_;
}
}
else
{
lean_dec_ref(v_cfg_2890_);
lean_dec(v_goals_2884_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
return v___x_2891_;
}
}
else
{
lean_dec_ref(v_cfg_2890_);
lean_dec(v_goals_2884_);
lean_dec_ref(v_ctx_2883_);
lean_dec(v_lemmas_2882_);
return v___x_2891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3049_, lean_object* v_lemmas_3050_, lean_object* v_ctx_3051_, lean_object* v_goals_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3049_, v_lemmas_3050_, v_ctx_3051_, v_goals_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3059_, lean_object* v_x_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
if (lean_obj_tag(v_x_3059_) == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = l_List_reverse___redArg(v_x_3060_);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
else
{
lean_object* v_head_3068_; lean_object* v_tail_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3092_; 
v_head_3068_ = lean_ctor_get(v_x_3059_, 0);
v_tail_3069_ = lean_ctor_get(v_x_3059_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_x_3059_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3071_ = v_x_3059_;
v_isShared_3072_ = v_isSharedCheck_3092_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_tail_3069_);
lean_inc(v_head_3068_);
lean_dec(v_x_3059_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3092_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_Expr_applySymm(v_head_3068_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___x_3073_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v_x_3060_);
lean_ctor_set(v___x_3071_, 0, v_a_3074_);
v___x_3076_ = v___x_3071_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3074_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_x_3060_);
v___x_3076_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
v_x_3059_ = v_tail_3069_;
v_x_3060_ = v___x_3076_;
goto _start;
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3091_; 
lean_del_object(v___x_3071_);
v_a_3079_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3081_ = v___x_3073_;
v_isShared_3082_ = v_isSharedCheck_3091_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3073_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3091_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
uint8_t v___y_3084_; uint8_t v___x_3089_; 
v___x_3089_ = l_Lean_Exception_isInterrupt(v_a_3079_);
if (v___x_3089_ == 0)
{
uint8_t v___x_3090_; 
lean_inc(v_a_3079_);
v___x_3090_ = l_Lean_Exception_isRuntime(v_a_3079_);
v___y_3084_ = v___x_3090_;
goto v___jp_3083_;
}
else
{
v___y_3084_ = v___x_3089_;
goto v___jp_3083_;
}
v___jp_3083_:
{
if (v___y_3084_ == 0)
{
lean_del_object(v___x_3081_);
lean_dec(v_a_3079_);
v_x_3059_ = v_tail_3069_;
goto _start;
}
else
{
lean_object* v___x_3087_; 
lean_dec(v_tail_3069_);
lean_dec(v_x_3060_);
if (v_isShared_3082_ == 0)
{
v___x_3087_ = v___x_3081_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3079_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3093_, v_x_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3101_, lean_object* v_hyps_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
if (v_symm_3101_ == 0)
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_hyps_3102_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = lean_box(0);
lean_inc(v_hyps_3102_);
v___x_3110_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3102_, v___x_3109_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = l_List_appendTR___redArg(v_hyps_3102_, v_a_3111_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_dec(v_hyps_3102_);
return v___x_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3120_, lean_object* v_hyps_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
uint8_t v_symm_boxed_3127_; lean_object* v_res_3128_; 
v_symm_boxed_3127_ = lean_unbox(v_symm_3120_);
v_res_3128_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3127_, v_hyps_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3129_, size_t v_sz_3130_, size_t v_i_3131_, lean_object* v_b_3132_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_usize_dec_lt(v_i_3131_, v_sz_3130_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_b_3132_);
return v___x_3135_;
}
else
{
lean_object* v_snd_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3154_; 
v_snd_3136_ = lean_ctor_get(v_b_3132_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_b_3132_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v_b_3132_, 0);
lean_dec(v_unused_3155_);
v___x_3138_ = v_b_3132_;
v_isShared_3139_ = v_isSharedCheck_3154_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_snd_3136_);
lean_dec(v_b_3132_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3154_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v_a_3142_; lean_object* v_a_3149_; 
v___x_3140_ = lean_box(0);
v_a_3149_ = lean_array_uget_borrowed(v_as_3129_, v_i_3131_);
if (lean_obj_tag(v_a_3149_) == 0)
{
v_a_3142_ = v_snd_3136_;
goto v___jp_3141_;
}
else
{
lean_object* v_val_3150_; uint8_t v___x_3151_; 
v_val_3150_ = lean_ctor_get(v_a_3149_, 0);
v___x_3151_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_inc(v_val_3150_);
v___x_3152_ = l_Lean_LocalDecl_toExpr(v_val_3150_);
v___x_3153_ = lean_array_push(v_snd_3136_, v___x_3152_);
v_a_3142_ = v___x_3153_;
goto v___jp_3141_;
}
else
{
v_a_3142_ = v_snd_3136_;
goto v___jp_3141_;
}
}
v___jp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v_a_3142_);
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3144_ = v___x_3138_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_a_3142_);
v___x_3144_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
size_t v___x_3145_; size_t v___x_3146_; 
v___x_3145_ = ((size_t)1ULL);
v___x_3146_ = lean_usize_add(v_i_3131_, v___x_3145_);
v_i_3131_ = v___x_3146_;
v_b_3132_ = v___x_3144_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3156_, lean_object* v_sz_3157_, lean_object* v_i_3158_, lean_object* v_b_3159_, lean_object* v___y_3160_){
_start:
{
size_t v_sz_boxed_3161_; size_t v_i_boxed_3162_; lean_object* v_res_3163_; 
v_sz_boxed_3161_ = lean_unbox_usize(v_sz_3157_);
lean_dec(v_sz_3157_);
v_i_boxed_3162_ = lean_unbox_usize(v_i_3158_);
lean_dec(v_i_3158_);
v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3156_, v_sz_boxed_3161_, v_i_boxed_3162_, v_b_3159_);
lean_dec_ref(v_as_3156_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3164_, size_t v_sz_3165_, size_t v_i_3166_, lean_object* v_b_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_lt(v_i_3166_, v_sz_3165_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_b_3167_);
return v___x_3176_;
}
else
{
lean_object* v_snd_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3195_; 
v_snd_3177_ = lean_ctor_get(v_b_3167_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_b_3167_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v_b_3167_, 0);
lean_dec(v_unused_3196_);
v___x_3179_ = v_b_3167_;
v_isShared_3180_ = v_isSharedCheck_3195_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_snd_3177_);
lean_dec(v_b_3167_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3195_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; lean_object* v_a_3183_; lean_object* v_a_3190_; 
v___x_3181_ = lean_box(0);
v_a_3190_ = lean_array_uget_borrowed(v_as_3164_, v_i_3166_);
if (lean_obj_tag(v_a_3190_) == 0)
{
v_a_3183_ = v_snd_3177_;
goto v___jp_3182_;
}
else
{
lean_object* v_val_3191_; uint8_t v___x_3192_; 
v_val_3191_ = lean_ctor_get(v_a_3190_, 0);
v___x_3192_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_inc(v_val_3191_);
v___x_3193_ = l_Lean_LocalDecl_toExpr(v_val_3191_);
v___x_3194_ = lean_array_push(v_snd_3177_, v___x_3193_);
v_a_3183_ = v___x_3194_;
goto v___jp_3182_;
}
else
{
v_a_3183_ = v_snd_3177_;
goto v___jp_3182_;
}
}
v___jp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v_a_3183_);
lean_ctor_set(v___x_3179_, 0, v___x_3181_);
v___x_3185_ = v___x_3179_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_a_3183_);
v___x_3185_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3166_, v___x_3186_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3164_, v_sz_3165_, v___x_3187_, v___x_3185_);
return v___x_3188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3197_, lean_object* v_sz_3198_, lean_object* v_i_3199_, lean_object* v_b_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
size_t v_sz_boxed_3208_; size_t v_i_boxed_3209_; lean_object* v_res_3210_; 
v_sz_boxed_3208_ = lean_unbox_usize(v_sz_3198_);
lean_dec(v_sz_3198_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3199_);
lean_dec(v_i_3199_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3197_, v_sz_boxed_3208_, v_i_boxed_3209_, v_b_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_as_3197_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_b_3214_){
_start:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v_b_3214_);
return v___x_3217_;
}
else
{
lean_object* v_snd_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3236_; 
v_snd_3218_ = lean_ctor_get(v_b_3214_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_b_3214_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_b_3214_, 0);
lean_dec(v_unused_3237_);
v___x_3220_ = v_b_3214_;
v_isShared_3221_ = v_isSharedCheck_3236_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_snd_3218_);
lean_dec(v_b_3214_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3236_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v_a_3224_; lean_object* v_a_3231_; 
v___x_3222_ = lean_box(0);
v_a_3231_ = lean_array_uget_borrowed(v_as_3211_, v_i_3213_);
if (lean_obj_tag(v_a_3231_) == 0)
{
v_a_3224_ = v_snd_3218_;
goto v___jp_3223_;
}
else
{
lean_object* v_val_3232_; uint8_t v___x_3233_; 
v_val_3232_ = lean_ctor_get(v_a_3231_, 0);
v___x_3233_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
lean_inc(v_val_3232_);
v___x_3234_ = l_Lean_LocalDecl_toExpr(v_val_3232_);
v___x_3235_ = lean_array_push(v_snd_3218_, v___x_3234_);
v_a_3224_ = v___x_3235_;
goto v___jp_3223_;
}
else
{
v_a_3224_ = v_snd_3218_;
goto v___jp_3223_;
}
}
v___jp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v_a_3224_);
lean_ctor_set(v___x_3220_, 0, v___x_3222_);
v___x_3226_ = v___x_3220_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_a_3224_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
size_t v___x_3227_; size_t v___x_3228_; 
v___x_3227_ = ((size_t)1ULL);
v___x_3228_ = lean_usize_add(v_i_3213_, v___x_3227_);
v_i_3213_ = v___x_3228_;
v_b_3214_ = v___x_3226_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3238_, lean_object* v_sz_3239_, lean_object* v_i_3240_, lean_object* v_b_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_sz_boxed_3243_; size_t v_i_boxed_3244_; lean_object* v_res_3245_; 
v_sz_boxed_3243_ = lean_unbox_usize(v_sz_3239_);
lean_dec(v_sz_3239_);
v_i_boxed_3244_ = lean_unbox_usize(v_i_3240_);
lean_dec(v_i_3240_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3238_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3241_);
lean_dec_ref(v_as_3238_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3246_, size_t v_sz_3247_, size_t v_i_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_usize_dec_lt(v_i_3248_, v_sz_3247_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_b_3249_);
return v___x_3258_;
}
else
{
lean_object* v_snd_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3277_; 
v_snd_3259_ = lean_ctor_get(v_b_3249_, 1);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_b_3249_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v_b_3249_, 0);
lean_dec(v_unused_3278_);
v___x_3261_ = v_b_3249_;
v_isShared_3262_ = v_isSharedCheck_3277_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_snd_3259_);
lean_dec(v_b_3249_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3277_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v_a_3265_; lean_object* v_a_3272_; 
v___x_3263_ = lean_box(0);
v_a_3272_ = lean_array_uget_borrowed(v_as_3246_, v_i_3248_);
if (lean_obj_tag(v_a_3272_) == 0)
{
v_a_3265_ = v_snd_3259_;
goto v___jp_3264_;
}
else
{
lean_object* v_val_3273_; uint8_t v___x_3274_; 
v_val_3273_ = lean_ctor_get(v_a_3272_, 0);
v___x_3274_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3273_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_inc(v_val_3273_);
v___x_3275_ = l_Lean_LocalDecl_toExpr(v_val_3273_);
v___x_3276_ = lean_array_push(v_snd_3259_, v___x_3275_);
v_a_3265_ = v___x_3276_;
goto v___jp_3264_;
}
else
{
v_a_3265_ = v_snd_3259_;
goto v___jp_3264_;
}
}
v___jp_3264_:
{
lean_object* v___x_3267_; 
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 1, v_a_3265_);
lean_ctor_set(v___x_3261_, 0, v___x_3263_);
v___x_3267_ = v___x_3261_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_a_3265_);
v___x_3267_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
size_t v___x_3268_; size_t v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = ((size_t)1ULL);
v___x_3269_ = lean_usize_add(v_i_3248_, v___x_3268_);
v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3246_, v_sz_3247_, v___x_3269_, v___x_3267_);
return v___x_3270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3279_, lean_object* v_sz_3280_, lean_object* v_i_3281_, lean_object* v_b_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
size_t v_sz_boxed_3290_; size_t v_i_boxed_3291_; lean_object* v_res_3292_; 
v_sz_boxed_3290_ = lean_unbox_usize(v_sz_3280_);
lean_dec(v_sz_3280_);
v_i_boxed_3291_ = lean_unbox_usize(v_i_3281_);
lean_dec(v_i_3281_);
v_res_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3279_, v_sz_boxed_3290_, v_i_boxed_3291_, v_b_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec_ref(v_as_3279_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3293_, lean_object* v_n_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
if (lean_obj_tag(v_n_3294_) == 0)
{
lean_object* v_cs_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3337_; 
v_cs_3303_ = lean_ctor_get(v_n_3294_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_n_3294_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3305_ = v_n_3294_;
v_isShared_3306_ = v_isSharedCheck_3337_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_cs_3303_);
lean_dec(v_n_3294_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3337_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; size_t v_sz_3309_; size_t v___x_3310_; lean_object* v___x_3311_; 
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
lean_ctor_set(v___x_3308_, 1, v_b_3295_);
v_sz_3309_ = lean_array_size(v_cs_3303_);
v___x_3310_ = ((size_t)0ULL);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3293_, v_cs_3303_, v_sz_3309_, v___x_3310_, v___x_3308_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec_ref(v_cs_3303_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3328_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3328_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3328_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_fst_3316_; 
v_fst_3316_ = lean_ctor_get(v_a_3312_, 0);
if (lean_obj_tag(v_fst_3316_) == 0)
{
lean_object* v_snd_3317_; lean_object* v___x_3319_; 
v_snd_3317_ = lean_ctor_get(v_a_3312_, 1);
lean_inc(v_snd_3317_);
lean_dec(v_a_3312_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 1);
lean_ctor_set(v___x_3305_, 0, v_snd_3317_);
v___x_3319_ = v___x_3305_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_snd_3317_);
v___x_3319_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3321_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3319_);
v___x_3321_ = v___x_3314_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
else
{
lean_object* v_val_3324_; lean_object* v___x_3326_; 
lean_inc_ref(v_fst_3316_);
lean_dec(v_a_3312_);
lean_del_object(v___x_3305_);
v_val_3324_ = lean_ctor_get(v_fst_3316_, 0);
lean_inc(v_val_3324_);
lean_dec_ref(v_fst_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v_val_3324_);
v___x_3326_ = v___x_3314_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_val_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_del_object(v___x_3305_);
v_a_3329_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3311_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3311_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
else
{
lean_object* v_vs_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3372_; 
v_vs_3338_ = lean_ctor_get(v_n_3294_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_n_3294_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3340_ = v_n_3294_;
v_isShared_3341_ = v_isSharedCheck_3372_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_vs_3338_);
lean_dec(v_n_3294_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3372_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; size_t v_sz_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v_b_3295_);
v_sz_3344_ = lean_array_size(v_vs_3338_);
v___x_3345_ = ((size_t)0ULL);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3338_, v_sz_3344_, v___x_3345_, v___x_3343_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec_ref(v_vs_3338_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3363_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3363_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3363_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_fst_3351_; 
v_fst_3351_ = lean_ctor_get(v_a_3347_, 0);
if (lean_obj_tag(v_fst_3351_) == 0)
{
lean_object* v_snd_3352_; lean_object* v___x_3354_; 
v_snd_3352_ = lean_ctor_get(v_a_3347_, 1);
lean_inc(v_snd_3352_);
lean_dec(v_a_3347_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_snd_3352_);
v___x_3354_ = v___x_3340_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_snd_3352_);
v___x_3354_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3356_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3354_);
v___x_3356_ = v___x_3349_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
else
{
lean_object* v_val_3359_; lean_object* v___x_3361_; 
lean_inc_ref(v_fst_3351_);
lean_dec(v_a_3347_);
lean_del_object(v___x_3340_);
v_val_3359_ = lean_ctor_get(v_fst_3351_, 0);
lean_inc(v_val_3359_);
lean_dec_ref(v_fst_3351_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v_val_3359_);
v___x_3361_ = v___x_3349_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_val_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_del_object(v___x_3340_);
v_a_3364_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3346_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3346_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3373_, lean_object* v_as_3374_, size_t v_sz_3375_, size_t v_i_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_usize_dec_lt(v_i_3376_, v_sz_3375_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_b_3377_);
return v___x_3386_;
}
else
{
lean_object* v_snd_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3421_; 
v_snd_3387_ = lean_ctor_get(v_b_3377_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_b_3377_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v_b_3377_, 0);
lean_dec(v_unused_3422_);
v___x_3389_ = v_b_3377_;
v_isShared_3390_ = v_isSharedCheck_3421_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_snd_3387_);
lean_dec(v_b_3377_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3421_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_array_uget_borrowed(v_as_3374_, v_i_3376_);
lean_inc(v_snd_3387_);
lean_inc(v_a_3391_);
v___x_3392_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3373_, v_a_3391_, v_snd_3387_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3412_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3412_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3412_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
if (lean_obj_tag(v_a_3393_) == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_a_3393_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3397_);
v___x_3399_ = v___x_3389_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_snd_3387_);
v___x_3399_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3401_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3399_);
v___x_3401_ = v___x_3395_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_del_object(v___x_3395_);
lean_dec(v_snd_3387_);
v_a_3404_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_a_3404_);
lean_dec_ref(v_a_3393_);
v___x_3405_ = lean_box(0);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 1, v_a_3404_);
lean_ctor_set(v___x_3389_, 0, v___x_3405_);
v___x_3407_ = v___x_3389_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_a_3404_);
v___x_3407_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
size_t v___x_3408_; size_t v___x_3409_; 
v___x_3408_ = ((size_t)1ULL);
v___x_3409_ = lean_usize_add(v_i_3376_, v___x_3408_);
v_i_3376_ = v___x_3409_;
v_b_3377_ = v___x_3407_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_del_object(v___x_3389_);
lean_dec(v_snd_3387_);
v_a_3413_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3392_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3392_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3423_, lean_object* v_as_3424_, lean_object* v_sz_3425_, lean_object* v_i_3426_, lean_object* v_b_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
size_t v_sz_boxed_3435_; size_t v_i_boxed_3436_; lean_object* v_res_3437_; 
v_sz_boxed_3435_ = lean_unbox_usize(v_sz_3425_);
lean_dec(v_sz_3425_);
v_i_boxed_3436_ = lean_unbox_usize(v_i_3426_);
lean_dec(v_i_3426_);
v_res_3437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3423_, v_as_3424_, v_sz_boxed_3435_, v_i_boxed_3436_, v_b_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_as_3424_);
lean_dec_ref(v_init_3423_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3438_, lean_object* v_n_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3438_, v_n_3439_, v_b_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v_init_3438_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3449_, lean_object* v_init_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_root_3458_; lean_object* v_tail_3459_; lean_object* v___x_3460_; 
v_root_3458_ = lean_ctor_get(v_t_3449_, 0);
lean_inc_ref(v_root_3458_);
v_tail_3459_ = lean_ctor_get(v_t_3449_, 1);
lean_inc_ref(v_tail_3459_);
lean_dec_ref(v_t_3449_);
lean_inc_ref(v_init_3450_);
v___x_3460_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3450_, v_root_3458_, v_init_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec_ref(v_init_3450_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3497_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3497_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3497_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
if (lean_obj_tag(v_a_3461_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; 
lean_dec_ref(v_tail_3459_);
v_a_3465_ = lean_ctor_get(v_a_3461_, 0);
lean_inc(v_a_3465_);
lean_dec_ref(v_a_3461_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v_a_3465_);
v___x_3467_ = v___x_3463_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; size_t v_sz_3472_; size_t v___x_3473_; lean_object* v___x_3474_; 
lean_del_object(v___x_3463_);
v_a_3469_ = lean_ctor_get(v_a_3461_, 0);
lean_inc(v_a_3469_);
lean_dec_ref(v_a_3461_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v_a_3469_);
v_sz_3472_ = lean_array_size(v_tail_3459_);
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3459_, v_sz_3472_, v___x_3473_, v___x_3471_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec_ref(v_tail_3459_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3488_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3488_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3488_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v_fst_3479_; 
v_fst_3479_ = lean_ctor_get(v_a_3475_, 0);
if (lean_obj_tag(v_fst_3479_) == 0)
{
lean_object* v_snd_3480_; lean_object* v___x_3482_; 
v_snd_3480_ = lean_ctor_get(v_a_3475_, 1);
lean_inc(v_snd_3480_);
lean_dec(v_a_3475_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v_snd_3480_);
v___x_3482_ = v___x_3477_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_snd_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
else
{
lean_object* v_val_3484_; lean_object* v___x_3486_; 
lean_inc_ref(v_fst_3479_);
lean_dec(v_a_3475_);
v_val_3484_ = lean_ctor_get(v_fst_3479_, 0);
lean_inc(v_val_3484_);
lean_dec_ref(v_fst_3479_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v_val_3484_);
v___x_3486_ = v___x_3477_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_val_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
v_a_3489_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3474_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3474_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_tail_3459_);
v_a_3498_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3460_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3460_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3506_, lean_object* v_init_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3506_, v_init_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_lctx_3525_; lean_object* v_decls_3526_; lean_object* v_hs_3527_; lean_object* v___x_3528_; 
v_lctx_3525_ = lean_ctor_get(v___y_3520_, 2);
v_decls_3526_ = lean_ctor_get(v_lctx_3525_, 1);
v_hs_3527_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
lean_inc_ref(v_decls_3526_);
v___x_3528_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3526_, v_hs_3527_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3537_, lean_object* v_cfg_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
if (v_only_3537_ == 0)
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_toApplyRulesConfig_3547_; lean_object* v_a_3548_; uint8_t v_symm_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_toApplyRulesConfig_3547_ = lean_ctor_get(v_cfg_3538_, 0);
v_a_3548_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3546_);
v_symm_3549_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3547_, sizeof(void*)*2 + 1);
v___x_3550_ = lean_array_to_list(v_a_3548_);
v___x_3551_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3549_, v___x_3550_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
return v___x_3551_;
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
v_a_3552_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3546_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3546_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_box(0);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
return v___x_3561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3562_, lean_object* v_cfg_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
uint8_t v_only_boxed_3571_; lean_object* v_res_3572_; 
v_only_boxed_3571_ = lean_unbox(v_only_3562_);
v_res_3572_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3571_, v_cfg_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec_ref(v_cfg_3563_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3573_, lean_object* v_lemmas_3574_, uint8_t v_only_3575_, lean_object* v_g_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_toApplyRulesConfig_3582_; uint8_t v_intro_3583_; uint8_t v_constructor_3584_; uint8_t v_suggestions_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3598_; 
v_toApplyRulesConfig_3582_ = lean_ctor_get(v_cfg_3573_, 0);
v_intro_3583_ = lean_ctor_get_uint8(v_cfg_3573_, sizeof(void*)*1 + 1);
v_constructor_3584_ = lean_ctor_get_uint8(v_cfg_3573_, sizeof(void*)*1 + 2);
v_suggestions_3585_ = lean_ctor_get_uint8(v_cfg_3573_, sizeof(void*)*1 + 3);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_cfg_3573_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3587_ = v_cfg_3573_;
v_isShared_3588_ = v_isSharedCheck_3598_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_toApplyRulesConfig_3582_);
lean_dec(v_cfg_3573_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3598_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v_ctx_3590_; uint8_t v___x_3591_; lean_object* v___x_3593_; 
v___x_3589_ = lean_box(v_only_3575_);
v_ctx_3590_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3590_, 0, v___x_3589_);
v___x_3591_ = 0;
if (v_isShared_3588_ == 0)
{
v___x_3593_ = v___x_3587_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_toApplyRulesConfig_3582_);
lean_ctor_set_uint8(v_reuseFailAlloc_3597_, sizeof(void*)*1 + 1, v_intro_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3597_, sizeof(void*)*1 + 2, v_constructor_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3597_, sizeof(void*)*1 + 3, v_suggestions_3585_);
v___x_3593_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
lean_ctor_set_uint8(v___x_3593_, sizeof(void*)*1, v___x_3591_);
v___x_3594_ = lean_box(0);
v___x_3595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3595_, 0, v_g_3576_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3593_, v_lemmas_3574_, v_ctx_3590_, v___x_3595_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3599_, lean_object* v_lemmas_3600_, lean_object* v_only_3601_, lean_object* v_g_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
uint8_t v_only_boxed_3608_; lean_object* v_res_3609_; 
v_only_boxed_3608_ = lean_unbox(v_only_3601_);
v_res_3609_ = l_Lean_MVarId_applyRules(v_cfg_3599_, v_lemmas_3600_, v_only_boxed_3608_, v_g_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3610_, size_t v_sz_3611_, size_t v_i_3612_, lean_object* v_b_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3610_, v_sz_3611_, v_i_3612_, v_b_3613_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3622_, lean_object* v_sz_3623_, lean_object* v_i_3624_, lean_object* v_b_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
size_t v_sz_boxed_3633_; size_t v_i_boxed_3634_; lean_object* v_res_3635_; 
v_sz_boxed_3633_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v_i_boxed_3634_ = lean_unbox_usize(v_i_3624_);
lean_dec(v_i_3624_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3622_, v_sz_boxed_3633_, v_i_boxed_3634_, v_b_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_as_3622_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3636_, size_t v_sz_3637_, size_t v_i_3638_, lean_object* v_b_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3636_, v_sz_3637_, v_i_3638_, v_b_3639_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3648_, lean_object* v_sz_3649_, lean_object* v_i_3650_, lean_object* v_b_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
size_t v_sz_boxed_3659_; size_t v_i_boxed_3660_; lean_object* v_res_3661_; 
v_sz_boxed_3659_ = lean_unbox_usize(v_sz_3649_);
lean_dec(v_sz_3649_);
v_i_boxed_3660_ = lean_unbox_usize(v_i_3650_);
lean_dec(v_i_3650_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3648_, v_sz_boxed_3659_, v_i_boxed_3660_, v_b_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec_ref(v_as_3648_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = lean_box(0);
v___x_3671_ = 1;
v___x_3672_ = l_Lean_Elab_Term_elabTerm(v_t_3662_, v___x_3670_, v___x_3671_, v___x_3671_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_a_3677_);
lean_dec_ref(v_a_3676_);
lean_dec(v_a_3675_);
lean_dec_ref(v_a_3674_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_ref_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_ref_3687_ = lean_ctor_get(v___y_3684_, 5);
v___x_3688_ = 0;
v___x_3689_ = l_Lean_SourceInfo_fromRef(v_ref_3687_, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
return v_res_3696_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3697_, lean_object* v_x_3698_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 0)
{
uint8_t v___x_3699_; 
v___x_3699_ = 0;
return v___x_3699_;
}
else
{
lean_object* v_head_3700_; lean_object* v_tail_3701_; uint8_t v___x_3702_; 
v_head_3700_ = lean_ctor_get(v_x_3698_, 0);
v_tail_3701_ = lean_ctor_get(v_x_3698_, 1);
v___x_3702_ = lean_expr_eqv(v_a_3697_, v_head_3700_);
if (v___x_3702_ == 0)
{
v_x_3698_ = v_tail_3701_;
goto _start;
}
else
{
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3704_, lean_object* v_x_3705_){
_start:
{
uint8_t v_res_3706_; lean_object* v_r_3707_; 
v_res_3706_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3704_, v_x_3705_);
lean_dec(v_x_3705_);
lean_dec_ref(v_a_3704_);
v_r_3707_ = lean_box(v_res_3706_);
return v_r_3707_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3708_, lean_object* v_x_3709_){
_start:
{
uint8_t v___x_3710_; 
v___x_3710_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3709_, v_ys_3708_);
if (v___x_3710_ == 0)
{
uint8_t v___x_3711_; 
v___x_3711_ = 1;
return v___x_3711_;
}
else
{
uint8_t v___x_3712_; 
v___x_3712_ = 0;
return v___x_3712_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3713_, lean_object* v_x_3714_){
_start:
{
uint8_t v_res_3715_; lean_object* v_r_3716_; 
v_res_3715_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3713_, v_x_3714_);
lean_dec_ref(v_x_3714_);
lean_dec(v_ys_3713_);
v_r_3716_ = lean_box(v_res_3715_);
return v_r_3716_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3717_, lean_object* v_ys_3718_){
_start:
{
lean_object* v___f_3719_; lean_object* v___x_3720_; 
v___f_3719_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3719_, 0, v_ys_3718_);
v___x_3720_ = l_List_filter___redArg(v___f_3719_, v_xs_3717_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3721_, lean_object* v_x_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
if (lean_obj_tag(v_x_3721_) == 0)
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = l_List_reverse___redArg(v_x_3722_);
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
else
{
lean_object* v_head_3732_; lean_object* v_tail_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3751_; 
v_head_3732_ = lean_ctor_get(v_x_3721_, 0);
v_tail_3733_ = lean_ctor_get(v_x_3721_, 1);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_x_3721_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3735_ = v_x_3721_;
v_isShared_3736_ = v_isSharedCheck_3751_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_tail_3733_);
lean_inc(v_head_3732_);
lean_dec(v_x_3721_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3751_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; 
v___x_3737_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3732_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 1, v_x_3722_);
lean_ctor_set(v___x_3735_, 0, v_a_3738_);
v___x_3740_ = v___x_3735_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3738_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_x_3722_);
v___x_3740_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v_x_3721_ = v_tail_3733_;
v_x_3722_ = v___x_3740_;
goto _start;
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3735_);
lean_dec(v_tail_3733_);
lean_dec(v_x_3722_);
v_a_3743_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3737_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3737_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3752_, lean_object* v_x_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3752_, v_x_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3762_, uint8_t v_noDefaults_3763_, uint8_t v_star_3764_, lean_object* v_cfg_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
if (v_noDefaults_3763_ == 0)
{
goto v___jp_3773_;
}
else
{
if (v_star_3764_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
lean_dec(v_remove_3762_);
v___x_3792_ = lean_box(0);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
else
{
goto v___jp_3773_;
}
}
v___jp_3773_:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = lean_box(0);
v___x_3777_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3762_, v___x_3776_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_toApplyRulesConfig_3778_; lean_object* v_a_3779_; uint8_t v_symm_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_toApplyRulesConfig_3778_ = lean_ctor_get(v_cfg_3765_, 0);
v_a_3779_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3777_);
v_symm_3780_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3778_, sizeof(void*)*2 + 1);
v___x_3781_ = lean_array_to_list(v_a_3775_);
v___x_3782_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3781_, v_a_3779_);
v___x_3783_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3780_, v___x_3782_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3783_;
}
else
{
lean_dec(v_a_3775_);
return v___x_3777_;
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec(v_remove_3762_);
v_a_3784_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3774_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3774_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3794_, lean_object* v_noDefaults_3795_, lean_object* v_star_3796_, lean_object* v_cfg_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
uint8_t v_noDefaults_boxed_3805_; uint8_t v_star_boxed_3806_; lean_object* v_res_3807_; 
v_noDefaults_boxed_3805_ = lean_unbox(v_noDefaults_3795_);
v_star_boxed_3806_ = lean_unbox(v_star_3796_);
v_res_3807_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3794_, v_noDefaults_boxed_3805_, v_star_boxed_3806_, v_cfg_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec_ref(v_cfg_3797_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3808_, size_t v_i_3809_, size_t v_stop_3810_, lean_object* v_b_3811_){
_start:
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_usize_dec_eq(v_i_3809_, v_stop_3810_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; lean_object* v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; 
v___x_3813_ = lean_array_uget_borrowed(v_as_3808_, v_i_3809_);
v___x_3814_ = l_Array_append___redArg(v_b_3811_, v___x_3813_);
v___x_3815_ = ((size_t)1ULL);
v___x_3816_ = lean_usize_add(v_i_3809_, v___x_3815_);
v_i_3809_ = v___x_3816_;
v_b_3811_ = v___x_3814_;
goto _start;
}
else
{
return v_b_3811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3818_, lean_object* v_i_3819_, lean_object* v_stop_3820_, lean_object* v_b_3821_){
_start:
{
size_t v_i_boxed_3822_; size_t v_stop_boxed_3823_; lean_object* v_res_3824_; 
v_i_boxed_3822_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_stop_boxed_3823_ = lean_unbox_usize(v_stop_3820_);
lean_dec(v_stop_3820_);
v_res_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3818_, v_i_boxed_3822_, v_stop_boxed_3823_, v_b_3821_);
lean_dec_ref(v_as_3818_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
if (lean_obj_tag(v_a_3825_) == 0)
{
lean_object* v___x_3827_; 
v___x_3827_ = l_List_reverse___redArg(v_a_3826_);
return v___x_3827_;
}
else
{
lean_object* v_head_3828_; lean_object* v_tail_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3838_; 
v_head_3828_ = lean_ctor_get(v_a_3825_, 0);
v_tail_3829_ = lean_ctor_get(v_a_3825_, 1);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_a_3825_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3831_ = v_a_3825_;
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_tail_3829_);
lean_inc(v_head_3828_);
lean_dec(v_a_3825_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3833_; lean_object* v___x_3835_; 
v___x_3833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3833_, 0, v_head_3828_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 1, v_a_3826_);
lean_ctor_set(v___x_3831_, 0, v___x_3833_);
v___x_3835_ = v___x_3831_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_a_3826_);
v___x_3835_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
v_a_3825_ = v_tail_3829_;
v_a_3826_ = v___x_3835_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3839_, size_t v_i_3840_, lean_object* v_bs_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
uint8_t v___x_3845_; 
v___x_3845_ = lean_usize_dec_lt(v_i_3840_, v_sz_3839_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_bs_3841_);
return v___x_3846_;
}
else
{
lean_object* v_v_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_v_3847_ = lean_array_uget_borrowed(v_bs_3841_, v_i_3840_);
v___x_3848_ = l_Lean_Syntax_getId(v_v_3847_);
v___x_3849_ = l_Lean_labelled(v___x_3848_, v___y_3842_, v___y_3843_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v_bs_x27_3852_; size_t v___x_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = lean_unsigned_to_nat(0u);
v_bs_x27_3852_ = lean_array_uset(v_bs_3841_, v_i_3840_, v___x_3851_);
v___x_3853_ = ((size_t)1ULL);
v___x_3854_ = lean_usize_add(v_i_3840_, v___x_3853_);
v___x_3855_ = lean_array_uset(v_bs_x27_3852_, v_i_3840_, v_a_3850_);
v_i_3840_ = v___x_3854_;
v_bs_3841_ = v___x_3855_;
goto _start;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v_bs_3841_);
v_a_3857_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3849_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3849_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3865_, lean_object* v_i_3866_, lean_object* v_bs_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
size_t v_sz_boxed_3871_; size_t v_i_boxed_3872_; lean_object* v_res_3873_; 
v_sz_boxed_3871_ = lean_unbox_usize(v_sz_3865_);
lean_dec(v_sz_3865_);
v_i_boxed_3872_ = lean_unbox_usize(v_i_3866_);
lean_dec(v_i_3866_);
v_res_3873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3871_, v_i_boxed_3872_, v_bs_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3874_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
if (lean_obj_tag(v_a_3892_) == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = l_List_reverse___redArg(v_a_3893_);
return v___x_3894_;
}
else
{
lean_object* v_head_3895_; lean_object* v_tail_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3905_; 
v_head_3895_ = lean_ctor_get(v_a_3892_, 0);
v_tail_3896_ = lean_ctor_get(v_a_3892_, 1);
v_isSharedCheck_3905_ = !lean_is_exclusive(v_a_3892_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3898_ = v_a_3892_;
v_isShared_3899_ = v_isSharedCheck_3905_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_tail_3896_);
lean_inc(v_head_3895_);
lean_dec(v_a_3892_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3905_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___f_3900_; lean_object* v___x_3902_; 
v___f_3900_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3900_, 0, v_head_3895_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 1, v_a_3893_);
lean_ctor_set(v___x_3898_, 0, v___f_3900_);
v___x_3902_ = v___x_3898_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___f_3900_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_a_3893_);
v___x_3902_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
v_a_3892_ = v_tail_3896_;
v_a_3893_ = v___x_3902_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3908_ = l_Lean_stringToMessageData(v___x_3907_);
return v___x_3908_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3911_ = l_String_toRawSubstring_x27(v___x_3910_);
return v___x_3911_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3916_ = l_String_toRawSubstring_x27(v___x_3915_);
return v___x_3916_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3921_ = l_String_toRawSubstring_x27(v___x_3920_);
return v___x_3921_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3926_ = l_String_toRawSubstring_x27(v___x_3925_);
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3957_ = l_Lean_stringToMessageData(v___x_3956_);
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3958_, uint8_t v_star_3959_, lean_object* v_add_3960_, lean_object* v_remove_3961_, lean_object* v_use_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___f_3993_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; 
v___x_3991_ = lean_box(v_noDefaults_3958_);
v___x_3992_ = lean_box(v_star_3959_);
lean_inc(v_remove_3961_);
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3993_, 0, v_remove_3961_);
lean_closure_set(v___f_3993_, 1, v___x_3991_);
lean_closure_set(v___f_3993_, 2, v___x_3992_);
if (v_star_3959_ == 0)
{
v___y_4010_ = v_a_3963_;
v___y_4011_ = v_a_3964_;
v___y_4012_ = v_a_3965_;
v___y_4013_ = v_a_3966_;
goto v___jp_4009_;
}
else
{
if (v_noDefaults_3958_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v___f_3993_);
lean_dec_ref(v_use_3962_);
lean_dec(v_remove_3961_);
lean_dec(v_add_3960_);
v___x_4072_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4073_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4072_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
else
{
v___y_4010_ = v_a_3963_;
v___y_4011_ = v_a_3964_;
v___y_4012_ = v_a_3965_;
v___y_4013_ = v_a_3966_;
goto v___jp_4009_;
}
}
v___jp_3968_:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___y_3970_);
lean_ctor_set(v___x_3971_, 1, v___y_3969_);
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
v___jp_3973_:
{
uint8_t v___x_3980_; 
v___x_3980_ = l_List_isEmpty___redArg(v_remove_3961_);
lean_dec(v_remove_3961_);
if (v___x_3980_ == 0)
{
if (v_noDefaults_3958_ == 0)
{
v___y_3969_ = v___y_3974_;
v___y_3970_ = v___y_3979_;
goto v___jp_3968_;
}
else
{
if (v_star_3959_ == 0)
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3974_);
v___x_3981_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3982_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3981_, v___y_3975_, v___y_3977_, v___y_3978_, v___y_3976_);
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3982_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
else
{
v___y_3969_ = v___y_3974_;
v___y_3970_ = v___y_3979_;
goto v___jp_3968_;
}
}
}
else
{
v___y_3969_ = v___y_3974_;
v___y_3970_ = v___y_3979_;
goto v___jp_3968_;
}
}
v___jp_3994_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_array_to_list(v___y_4001_);
lean_inc(v___y_3996_);
v___x_4003_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_4002_, v___y_3996_);
if (v_noDefaults_3958_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3960_, v___y_3996_);
v___x_4005_ = l_List_appendTR___redArg(v___x_4004_, v___x_4003_);
v___x_4006_ = l_List_appendTR___redArg(v___x_4005_, v___y_3995_);
v___y_3974_ = v___f_3993_;
v___y_3975_ = v___y_3997_;
v___y_3976_ = v___y_3998_;
v___y_3977_ = v___y_3999_;
v___y_3978_ = v___y_4000_;
v___y_3979_ = v___x_4006_;
goto v___jp_3973_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_dec(v___y_3995_);
v___x_4007_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3960_, v___y_3996_);
v___x_4008_ = l_List_appendTR___redArg(v___x_4007_, v___x_4003_);
v___y_3974_ = v___f_3993_;
v___y_3975_ = v___y_3997_;
v___y_3976_ = v___y_3998_;
v___y_3977_ = v___y_3999_;
v___y_3978_ = v___y_4000_;
v___y_3979_ = v___x_4008_;
goto v___jp_3973_;
}
}
v___jp_4009_:
{
lean_object* v_ref_4014_; lean_object* v_quotContext_4015_; lean_object* v_currMacroScope_4016_; lean_object* v___x_4017_; lean_object* v_a_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v_a_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v_a_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; size_t v_sz_4030_; size_t v___x_4031_; lean_object* v___x_4032_; 
v_ref_4014_ = lean_ctor_get(v___y_4012_, 5);
v_quotContext_4015_ = lean_ctor_get(v___y_4012_, 10);
v_currMacroScope_4016_ = lean_ctor_get(v___y_4012_, 11);
v___x_4017_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_a_4018_);
lean_dec_ref(v___x_4017_);
v___x_4019_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4020_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref(v___x_4020_);
v___x_4022_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_4016_, 2);
lean_inc_n(v_quotContext_4015_, 2);
v___x_4023_ = l_Lean_addMacroScope(v_quotContext_4015_, v___x_4022_, v_currMacroScope_4016_);
v___x_4024_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4025_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref(v___x_4025_);
v___x_4027_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4028_ = l_Lean_addMacroScope(v_quotContext_4015_, v___x_4027_, v_currMacroScope_4016_);
v___x_4029_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4030_ = lean_array_size(v_use_3962_);
v___x_4031_ = ((size_t)0ULL);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4030_, v___x_4031_, v_use_3962_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref(v___x_4032_);
v___x_4034_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_4016_, 2);
lean_inc_n(v_quotContext_4015_, 2);
v___x_4035_ = l_Lean_addMacroScope(v_quotContext_4015_, v___x_4034_, v_currMacroScope_4016_);
v___x_4036_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4037_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4038_ = l_Lean_addMacroScope(v_quotContext_4015_, v___x_4037_, v_currMacroScope_4016_);
v___x_4039_ = 0;
v___x_4040_ = l_Lean_SourceInfo_fromRef(v_ref_4014_, v___x_4039_);
v___x_4041_ = lean_box(0);
v___x_4042_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4043_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4040_);
lean_ctor_set(v___x_4043_, 1, v___x_4019_);
lean_ctor_set(v___x_4043_, 2, v___x_4023_);
lean_ctor_set(v___x_4043_, 3, v___x_4042_);
v___x_4044_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4045_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4045_, 0, v_a_4018_);
lean_ctor_set(v___x_4045_, 1, v___x_4024_);
lean_ctor_set(v___x_4045_, 2, v___x_4028_);
lean_ctor_set(v___x_4045_, 3, v___x_4044_);
v___x_4046_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4047_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4047_, 0, v_a_4021_);
lean_ctor_set(v___x_4047_, 1, v___x_4029_);
lean_ctor_set(v___x_4047_, 2, v___x_4035_);
lean_ctor_set(v___x_4047_, 3, v___x_4046_);
v___x_4048_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4049_, 0, v_a_4026_);
lean_ctor_set(v___x_4049_, 1, v___x_4036_);
lean_ctor_set(v___x_4049_, 2, v___x_4038_);
lean_ctor_set(v___x_4049_, 3, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___x_4041_);
v___x_4051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4047_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4045_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4043_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4053_, v___x_4041_);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4057_ = lean_array_get_size(v_a_4033_);
v___x_4058_ = lean_nat_dec_lt(v___x_4055_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_dec(v_a_4033_);
v___y_3995_ = v___x_4054_;
v___y_3996_ = v___x_4041_;
v___y_3997_ = v___y_4010_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4012_;
v___y_4001_ = v___x_4056_;
goto v___jp_3994_;
}
else
{
uint8_t v___x_4059_; 
v___x_4059_ = lean_nat_dec_le(v___x_4057_, v___x_4057_);
if (v___x_4059_ == 0)
{
if (v___x_4058_ == 0)
{
lean_dec(v_a_4033_);
v___y_3995_ = v___x_4054_;
v___y_3996_ = v___x_4041_;
v___y_3997_ = v___y_4010_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4012_;
v___y_4001_ = v___x_4056_;
goto v___jp_3994_;
}
else
{
size_t v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_usize_of_nat(v___x_4057_);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4033_, v___x_4031_, v___x_4060_, v___x_4056_);
lean_dec(v_a_4033_);
v___y_3995_ = v___x_4054_;
v___y_3996_ = v___x_4041_;
v___y_3997_ = v___y_4010_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4012_;
v___y_4001_ = v___x_4061_;
goto v___jp_3994_;
}
}
else
{
size_t v___x_4062_; lean_object* v___x_4063_; 
v___x_4062_ = lean_usize_of_nat(v___x_4057_);
v___x_4063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4033_, v___x_4031_, v___x_4062_, v___x_4056_);
lean_dec(v_a_4033_);
v___y_3995_ = v___x_4054_;
v___y_3996_ = v___x_4041_;
v___y_3997_ = v___y_4010_;
v___y_3998_ = v___y_4013_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4012_;
v___y_4001_ = v___x_4063_;
goto v___jp_3994_;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v___x_4028_);
lean_dec(v_a_4026_);
lean_dec(v___x_4023_);
lean_dec(v_a_4021_);
lean_dec(v_a_4018_);
lean_dec_ref(v___f_3993_);
lean_dec(v_remove_3961_);
lean_dec(v_add_3960_);
v_a_4064_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4032_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4032_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4082_, lean_object* v_star_4083_, lean_object* v_add_4084_, lean_object* v_remove_4085_, lean_object* v_use_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
uint8_t v_noDefaults_boxed_4092_; uint8_t v_star_boxed_4093_; lean_object* v_res_4094_; 
v_noDefaults_boxed_4092_ = lean_unbox(v_noDefaults_4082_);
v_star_boxed_4093_ = lean_unbox(v_star_4083_);
v_res_4094_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4092_, v_star_boxed_4093_, v_add_4084_, v_remove_4085_, v_use_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4095_, size_t v_i_4096_, lean_object* v_bs_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4095_, v_i_4096_, v_bs_4097_, v___y_4100_, v___y_4101_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4104_, lean_object* v_i_4105_, lean_object* v_bs_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
size_t v_sz_boxed_4112_; size_t v_i_boxed_4113_; lean_object* v_res_4114_; 
v_sz_boxed_4112_ = lean_unbox_usize(v_sz_4104_);
lean_dec(v_sz_4104_);
v_i_boxed_4113_ = lean_unbox_usize(v_i_4105_);
lean_dec(v_i_4105_);
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4112_, v_i_boxed_4113_, v_bs_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4114_;
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
