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
lean_object* v___x_90_; lean_object* v_traceState_91_; lean_object* v_traces_92_; lean_object* v___x_93_; lean_object* v_traceState_94_; lean_object* v_env_95_; lean_object* v_nextMacroScope_96_; lean_object* v_ngen_97_; lean_object* v_auxDeclNGen_98_; lean_object* v_cache_99_; lean_object* v_messages_100_; lean_object* v_infoState_101_; lean_object* v_snapshotTasks_102_; lean_object* v_newDecls_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_122_; 
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
v_newDecls_103_ = lean_ctor_get(v___x_93_, 9);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_122_ == 0)
{
v___x_105_ = v___x_93_;
v_isShared_106_ = v_isSharedCheck_122_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_newDecls_103_);
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
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_122_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
uint64_t v_tid_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_120_; 
v_tid_107_ = lean_ctor_get_uint64(v_traceState_94_, sizeof(void*)*1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_traceState_94_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; 
v_unused_121_ = lean_ctor_get(v_traceState_94_, 0);
lean_dec(v_unused_121_);
v___x_109_ = v_traceState_94_;
v_isShared_110_ = v_isSharedCheck_120_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_traceState_94_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_120_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_111_);
lean_ctor_set_uint64(v_reuseFailAlloc_119_, sizeof(void*)*1, v_tid_107_);
v___x_113_ = v_reuseFailAlloc_119_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 4, v___x_113_);
v___x_115_ = v___x_105_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_env_95_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_nextMacroScope_96_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_ngen_97_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v_auxDeclNGen_98_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_118_, 5, v_cache_99_);
lean_ctor_set(v_reuseFailAlloc_118_, 6, v_messages_100_);
lean_ctor_set(v_reuseFailAlloc_118_, 7, v_infoState_101_);
lean_ctor_set(v_reuseFailAlloc_118_, 8, v_snapshotTasks_102_);
lean_ctor_set(v_reuseFailAlloc_118_, 9, v_newDecls_103_);
v___x_115_ = v_reuseFailAlloc_118_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_st_ref_set(v___y_88_, v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_traces_92_);
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_123_);
lean_dec(v___y_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_138_, lean_object* v_opt_139_){
_start:
{
lean_object* v_name_140_; lean_object* v_defValue_141_; lean_object* v_map_142_; lean_object* v___x_143_; 
v_name_140_ = lean_ctor_get(v_opt_139_, 0);
v_defValue_141_ = lean_ctor_get(v_opt_139_, 1);
v_map_142_ = lean_ctor_get(v_opts_138_, 0);
v___x_143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_142_, v_name_140_);
if (lean_obj_tag(v___x_143_) == 0)
{
uint8_t v___x_144_; 
v___x_144_ = lean_unbox(v_defValue_141_);
return v___x_144_;
}
else
{
lean_object* v_val_145_; 
v_val_145_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_val_145_);
lean_dec_ref(v___x_143_);
if (lean_obj_tag(v_val_145_) == 1)
{
uint8_t v_v_146_; 
v_v_146_ = lean_ctor_get_uint8(v_val_145_, 0);
lean_dec_ref(v_val_145_);
return v_v_146_;
}
else
{
uint8_t v___x_147_; 
lean_dec(v_val_145_);
v___x_147_ = lean_unbox(v_defValue_141_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_148_, lean_object* v_opt_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_148_, v_opt_149_);
lean_dec_ref(v_opt_149_);
lean_dec_ref(v_opts_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_saveState___redArg(v___y_154_, v___y_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref(v___x_158_);
lean_inc(v___y_156_);
lean_inc_ref(v___y_155_);
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
v___x_160_ = lean_apply_5(v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, lean_box(0));
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
lean_dec(v_a_159_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_199_; 
v_a_170_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_199_ == 0)
{
v___x_172_ = v___x_160_;
v_isShared_173_ = v_isSharedCheck_199_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_160_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_199_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___y_175_; uint8_t v___x_197_; 
v___x_197_ = l_Lean_Exception_isInterrupt(v_a_170_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
lean_inc(v_a_170_);
v___x_198_ = l_Lean_Exception_isRuntime(v_a_170_);
v___y_175_ = v___x_198_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_197_;
goto v___jp_174_;
}
v___jp_174_:
{
if (v___y_175_ == 0)
{
lean_object* v___x_176_; 
lean_del_object(v___x_172_);
lean_dec(v_a_170_);
v___x_176_ = l_Lean_Meta_SavedState_restore___redArg(v_a_159_, v___y_154_, v___y_156_);
lean_dec(v_a_159_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; 
v_unused_185_ = lean_ctor_get(v___x_176_, 0);
lean_dec(v_unused_185_);
v___x_178_ = v___x_176_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_dec(v___x_176_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_176_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_176_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_a_159_);
if (v_isShared_173_ == 0)
{
v___x_195_ = v___x_172_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_170_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_x_152_);
v_a_200_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_158_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_158_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_215_, lean_object* v_x_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_223_, v_x_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_230_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_234_, lean_object* v_x_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_241_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_242_ = l_Lean_MessageData_ofExpr(v_e_234_);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec_ref(v_x_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_253_, uint8_t v___x_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v_x_256_);
return v___x_262_;
}
else
{
lean_object* v_head_263_; lean_object* v_tail_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_288_; 
v_head_263_ = lean_ctor_get(v_x_255_, 0);
v_tail_264_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_288_ == 0)
{
v___x_266_ = v_x_255_;
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_tail_264_);
lean_inc(v_head_263_);
lean_dec(v_x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v_a_269_; lean_object* v___x_275_; 
lean_inc(v_head_263_);
v___x_275_ = l_Lean_MVarId_inferInstance(v_head_263_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref(v___x_275_);
v_a_269_ = v___x_253_;
goto v___jp_268_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_287_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_287_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_287_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
uint8_t v___y_281_; uint8_t v___x_285_; 
v___x_285_ = l_Lean_Exception_isInterrupt(v_a_276_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
lean_inc(v_a_276_);
v___x_286_ = l_Lean_Exception_isRuntime(v_a_276_);
v___y_281_ = v___x_286_;
goto v___jp_280_;
}
else
{
v___y_281_ = v___x_285_;
goto v___jp_280_;
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
lean_del_object(v___x_278_);
lean_dec(v_a_276_);
v_a_269_ = v___x_254_;
goto v___jp_268_;
}
else
{
lean_object* v___x_283_; 
lean_del_object(v___x_266_);
lean_dec(v_tail_264_);
lean_dec(v_head_263_);
lean_dec(v_x_256_);
if (v_isShared_279_ == 0)
{
v___x_283_ = v___x_278_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_276_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
v___jp_268_:
{
if (v_a_269_ == 0)
{
lean_del_object(v___x_266_);
lean_dec(v_head_263_);
v_x_255_ = v_tail_264_;
goto _start;
}
else
{
lean_object* v___x_272_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v_x_256_);
v___x_272_ = v___x_266_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_head_263_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_x_256_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_x_255_ = v_tail_264_;
v_x_256_ = v___x_272_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_289_, lean_object* v___x_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_14221__boxed_298_; uint8_t v___x_14222__boxed_299_; lean_object* v_res_300_; 
v___x_14221__boxed_298_ = lean_unbox(v___x_289_);
v___x_14222__boxed_299_ = lean_unbox(v___x_290_);
v_res_300_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_14221__boxed_298_, v___x_14222__boxed_299_, v_x_291_, v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v_x_301_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v_x_301_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v_x_301_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 1);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_a_311_ = lean_ctor_get(v_x_301_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v_x_301_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v_x_301_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 0);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg___boxed(lean_object* v_x_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_319_);
return v_res_321_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_e_322_){
_start:
{
if (lean_obj_tag(v_e_322_) == 0)
{
uint8_t v___x_323_; 
v___x_323_ = 2;
return v___x_323_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_e_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_e_325_);
lean_dec_ref(v_e_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_328_, lean_object* v_opt_329_){
_start:
{
lean_object* v_name_330_; lean_object* v_defValue_331_; lean_object* v_map_332_; lean_object* v___x_333_; 
v_name_330_ = lean_ctor_get(v_opt_329_, 0);
v_defValue_331_ = lean_ctor_get(v_opt_329_, 1);
v_map_332_ = lean_ctor_get(v_opts_328_, 0);
v___x_333_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_332_, v_name_330_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_inc(v_defValue_331_);
return v_defValue_331_;
}
else
{
lean_object* v_val_334_; 
v_val_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref(v___x_333_);
if (lean_obj_tag(v_val_334_) == 3)
{
lean_object* v_v_335_; 
v_v_335_ = lean_ctor_get(v_val_334_, 0);
lean_inc(v_v_335_);
lean_dec_ref(v_val_334_);
return v_v_335_;
}
else
{
lean_dec(v_val_334_);
lean_inc(v_defValue_331_);
return v_defValue_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_336_, lean_object* v_opt_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_336_, v_opt_337_);
lean_dec_ref(v_opt_337_);
lean_dec_ref(v_opts_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(size_t v_sz_339_, size_t v_i_340_, lean_object* v_bs_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_340_, v_sz_339_);
if (v___x_342_ == 0)
{
return v_bs_341_;
}
else
{
lean_object* v_v_343_; lean_object* v_msg_344_; lean_object* v___x_345_; lean_object* v_bs_x27_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v_v_343_ = lean_array_uget_borrowed(v_bs_341_, v_i_340_);
v_msg_344_ = lean_ctor_get(v_v_343_, 1);
lean_inc_ref(v_msg_344_);
v___x_345_ = lean_unsigned_to_nat(0u);
v_bs_x27_346_ = lean_array_uset(v_bs_341_, v_i_340_, v___x_345_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_add(v_i_340_, v___x_347_);
v___x_349_ = lean_array_uset(v_bs_x27_346_, v_i_340_, v_msg_344_);
v_i_340_ = v___x_348_;
v_bs_341_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_351_, lean_object* v_i_352_, lean_object* v_bs_353_){
_start:
{
size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v_sz_boxed_354_ = lean_unbox_usize(v_sz_351_);
lean_dec(v_sz_351_);
v_i_boxed_355_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_boxed_354_, v_i_boxed_355_, v_bs_353_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(lean_object* v_msgData_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v_lctx_367_; lean_object* v_options_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_363_ = lean_st_ref_get(v___y_361_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_363_);
v___x_365_ = lean_st_ref_get(v___y_359_);
v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_mctx_366_);
lean_dec(v___x_365_);
v_lctx_367_ = lean_ctor_get(v___y_358_, 2);
v_options_368_ = lean_ctor_get(v___y_360_, 2);
lean_inc_ref(v_options_368_);
lean_inc_ref(v_lctx_367_);
v___x_369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_369_, 0, v_env_364_);
lean_ctor_set(v___x_369_, 1, v_mctx_366_);
lean_ctor_set(v___x_369_, 2, v_lctx_367_);
lean_ctor_set(v___x_369_, 3, v_options_368_);
v___x_370_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_msgData_357_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6___boxed(lean_object* v_msgData_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msgData_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_oldTraces_379_, lean_object* v_data_380_, lean_object* v_ref_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_fileName_388_; lean_object* v_fileMap_389_; lean_object* v_options_390_; lean_object* v_currRecDepth_391_; lean_object* v_maxRecDepth_392_; lean_object* v_ref_393_; lean_object* v_currNamespace_394_; lean_object* v_openDecls_395_; lean_object* v_initHeartbeats_396_; lean_object* v_maxHeartbeats_397_; lean_object* v_quotContext_398_; lean_object* v_currMacroScope_399_; uint8_t v_diag_400_; lean_object* v_cancelTk_x3f_401_; uint8_t v_suppressElabErrors_402_; lean_object* v_inheritedTraceOptions_403_; lean_object* v___x_404_; lean_object* v_traceState_405_; lean_object* v_traces_406_; lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v___x_409_; size_t v_sz_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v_msg_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_453_; 
v_fileName_388_ = lean_ctor_get(v___y_385_, 0);
v_fileMap_389_ = lean_ctor_get(v___y_385_, 1);
v_options_390_ = lean_ctor_get(v___y_385_, 2);
v_currRecDepth_391_ = lean_ctor_get(v___y_385_, 3);
v_maxRecDepth_392_ = lean_ctor_get(v___y_385_, 4);
v_ref_393_ = lean_ctor_get(v___y_385_, 5);
v_currNamespace_394_ = lean_ctor_get(v___y_385_, 6);
v_openDecls_395_ = lean_ctor_get(v___y_385_, 7);
v_initHeartbeats_396_ = lean_ctor_get(v___y_385_, 8);
v_maxHeartbeats_397_ = lean_ctor_get(v___y_385_, 9);
v_quotContext_398_ = lean_ctor_get(v___y_385_, 10);
v_currMacroScope_399_ = lean_ctor_get(v___y_385_, 11);
v_diag_400_ = lean_ctor_get_uint8(v___y_385_, sizeof(void*)*14);
v_cancelTk_x3f_401_ = lean_ctor_get(v___y_385_, 12);
v_suppressElabErrors_402_ = lean_ctor_get_uint8(v___y_385_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_403_ = lean_ctor_get(v___y_385_, 13);
v___x_404_ = lean_st_ref_get(v___y_386_);
v_traceState_405_ = lean_ctor_get(v___x_404_, 4);
lean_inc_ref(v_traceState_405_);
lean_dec(v___x_404_);
v_traces_406_ = lean_ctor_get(v_traceState_405_, 0);
lean_inc_ref(v_traces_406_);
lean_dec_ref(v_traceState_405_);
v_ref_407_ = l_Lean_replaceRef(v_ref_381_, v_ref_393_);
lean_inc_ref(v_inheritedTraceOptions_403_);
lean_inc(v_cancelTk_x3f_401_);
lean_inc(v_currMacroScope_399_);
lean_inc(v_quotContext_398_);
lean_inc(v_maxHeartbeats_397_);
lean_inc(v_initHeartbeats_396_);
lean_inc(v_openDecls_395_);
lean_inc(v_currNamespace_394_);
lean_inc(v_maxRecDepth_392_);
lean_inc(v_currRecDepth_391_);
lean_inc_ref(v_options_390_);
lean_inc_ref(v_fileMap_389_);
lean_inc_ref(v_fileName_388_);
v___x_408_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_408_, 0, v_fileName_388_);
lean_ctor_set(v___x_408_, 1, v_fileMap_389_);
lean_ctor_set(v___x_408_, 2, v_options_390_);
lean_ctor_set(v___x_408_, 3, v_currRecDepth_391_);
lean_ctor_set(v___x_408_, 4, v_maxRecDepth_392_);
lean_ctor_set(v___x_408_, 5, v_ref_407_);
lean_ctor_set(v___x_408_, 6, v_currNamespace_394_);
lean_ctor_set(v___x_408_, 7, v_openDecls_395_);
lean_ctor_set(v___x_408_, 8, v_initHeartbeats_396_);
lean_ctor_set(v___x_408_, 9, v_maxHeartbeats_397_);
lean_ctor_set(v___x_408_, 10, v_quotContext_398_);
lean_ctor_set(v___x_408_, 11, v_currMacroScope_399_);
lean_ctor_set(v___x_408_, 12, v_cancelTk_x3f_401_);
lean_ctor_set(v___x_408_, 13, v_inheritedTraceOptions_403_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*14, v_diag_400_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*14 + 1, v_suppressElabErrors_402_);
v___x_409_ = l_Lean_PersistentArray_toArray___redArg(v_traces_406_);
lean_dec_ref(v_traces_406_);
v_sz_410_ = lean_array_size(v___x_409_);
v___x_411_ = ((size_t)0ULL);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_410_, v___x_411_, v___x_409_);
v_msg_413_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_413_, 0, v_data_380_);
lean_ctor_set(v_msg_413_, 1, v_msg_382_);
lean_ctor_set(v_msg_413_, 2, v___x_412_);
v___x_414_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_413_, v___y_383_, v___y_384_, v___x_408_, v___y_386_);
lean_dec_ref(v___x_408_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_453_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_453_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_453_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v_traceState_420_; lean_object* v_env_421_; lean_object* v_nextMacroScope_422_; lean_object* v_ngen_423_; lean_object* v_auxDeclNGen_424_; lean_object* v_cache_425_; lean_object* v_messages_426_; lean_object* v_infoState_427_; lean_object* v_snapshotTasks_428_; lean_object* v_newDecls_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_452_; 
v___x_419_ = lean_st_ref_take(v___y_386_);
v_traceState_420_ = lean_ctor_get(v___x_419_, 4);
v_env_421_ = lean_ctor_get(v___x_419_, 0);
v_nextMacroScope_422_ = lean_ctor_get(v___x_419_, 1);
v_ngen_423_ = lean_ctor_get(v___x_419_, 2);
v_auxDeclNGen_424_ = lean_ctor_get(v___x_419_, 3);
v_cache_425_ = lean_ctor_get(v___x_419_, 5);
v_messages_426_ = lean_ctor_get(v___x_419_, 6);
v_infoState_427_ = lean_ctor_get(v___x_419_, 7);
v_snapshotTasks_428_ = lean_ctor_get(v___x_419_, 8);
v_newDecls_429_ = lean_ctor_get(v___x_419_, 9);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_452_ == 0)
{
v___x_431_ = v___x_419_;
v_isShared_432_ = v_isSharedCheck_452_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_newDecls_429_);
lean_inc(v_snapshotTasks_428_);
lean_inc(v_infoState_427_);
lean_inc(v_messages_426_);
lean_inc(v_cache_425_);
lean_inc(v_traceState_420_);
lean_inc(v_auxDeclNGen_424_);
lean_inc(v_ngen_423_);
lean_inc(v_nextMacroScope_422_);
lean_inc(v_env_421_);
lean_dec(v___x_419_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_452_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint64_t v_tid_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_450_; 
v_tid_433_ = lean_ctor_get_uint64(v_traceState_420_, sizeof(void*)*1);
v_isSharedCheck_450_ = !lean_is_exclusive(v_traceState_420_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v_traceState_420_, 0);
lean_dec(v_unused_451_);
v___x_435_ = v_traceState_420_;
v_isShared_436_ = v_isSharedCheck_450_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_traceState_420_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_450_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_ref_381_);
lean_ctor_set(v___x_437_, 1, v_a_415_);
v___x_438_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_379_, v___x_437_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_438_);
lean_ctor_set_uint64(v_reuseFailAlloc_449_, sizeof(void*)*1, v_tid_433_);
v___x_440_ = v_reuseFailAlloc_449_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 4, v___x_440_);
v___x_442_ = v___x_431_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_env_421_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_nextMacroScope_422_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_ngen_423_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_auxDeclNGen_424_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_448_, 5, v_cache_425_);
lean_ctor_set(v_reuseFailAlloc_448_, 6, v_messages_426_);
lean_ctor_set(v_reuseFailAlloc_448_, 7, v_infoState_427_);
lean_ctor_set(v_reuseFailAlloc_448_, 8, v_snapshotTasks_428_);
lean_ctor_set(v_reuseFailAlloc_448_, 9, v_newDecls_429_);
v___x_442_ = v_reuseFailAlloc_448_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = lean_st_ref_set(v___y_386_, v___x_442_);
v___x_444_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_444_);
v___x_446_ = v___x_417_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_oldTraces_454_, lean_object* v_data_455_, lean_object* v_ref_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_454_, v_data_455_, v_ref_456_, v_msg_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_467_; double v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_float_of_nat(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5(void){
_start:
{
lean_object* v___x_472_; double v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1000u);
v___x_473_ = lean_float_of_nat(v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_474_, uint8_t v_collapsed_475_, lean_object* v_tag_476_, lean_object* v_opts_477_, uint8_t v_clsEnabled_478_, lean_object* v_oldTraces_479_, lean_object* v_msg_480_, lean_object* v_resStartStop_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_587_; 
v_fst_487_ = lean_ctor_get(v_resStartStop_481_, 0);
v_snd_488_ = lean_ctor_get(v_resStartStop_481_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_resStartStop_481_);
if (v_isSharedCheck_587_ == 0)
{
v___x_490_ = v_resStartStop_481_;
v_isShared_491_ = v_isSharedCheck_587_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_resStartStop_481_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_587_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_data_495_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_586_; 
v_fst_506_ = lean_ctor_get(v_snd_488_, 0);
v_snd_507_ = lean_ctor_get(v_snd_488_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_snd_488_);
if (v_isSharedCheck_586_ == 0)
{
v___x_509_ = v_snd_488_;
v_isShared_510_ = v_isSharedCheck_586_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_snd_488_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_586_;
goto v_resetjp_508_;
}
v___jp_492_:
{
lean_object* v___x_496_; 
lean_inc(v___y_494_);
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_479_, v_data_495_, v___y_494_, v___y_493_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v___x_496_);
v___x_497_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_487_);
return v___x_497_;
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_fst_487_);
v_a_498_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_496_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
v_resetjp_508_:
{
lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___y_514_; lean_object* v_a_515_; uint8_t v___y_539_; double v___y_571_; 
v___x_511_ = l_Lean_trace_profiler;
v___x_512_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_477_, v___x_511_);
if (v___x_512_ == 0)
{
v___y_539_ = v___x_512_;
goto v___jp_538_;
}
else
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = l_Lean_trace_profiler_useHeartbeats;
v___x_577_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_477_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; double v___x_580_; double v___x_581_; double v___x_582_; 
v___x_578_ = l_Lean_trace_profiler_threshold;
v___x_579_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_477_, v___x_578_);
v___x_580_ = lean_float_of_nat(v___x_579_);
v___x_581_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5);
v___x_582_ = lean_float_div(v___x_580_, v___x_581_);
v___y_571_ = v___x_582_;
goto v___jp_570_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; double v___x_585_; 
v___x_583_ = l_Lean_trace_profiler_threshold;
v___x_584_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_477_, v___x_583_);
v___x_585_ = lean_float_of_nat(v___x_584_);
v___y_571_ = v___x_585_;
goto v___jp_570_;
}
}
v___jp_513_:
{
uint8_t v_result_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_result_516_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_fst_487_);
v___x_517_ = l_Lean_TraceResult_toEmoji(v_result_516_);
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
v___x_519_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 7);
lean_ctor_set(v___x_509_, 1, v___x_519_);
lean_ctor_set(v___x_509_, 0, v___x_518_);
v___x_521_ = v___x_509_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_532_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v_m_523_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 7);
lean_ctor_set(v___x_490_, 1, v_a_515_);
lean_ctor_set(v___x_490_, 0, v___x_521_);
v_m_523_ = v___x_490_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_515_);
v_m_523_ = v_reuseFailAlloc_531_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; double v___x_526_; lean_object* v_data_527_; 
v___x_524_ = lean_box(v_result_516_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
lean_inc_ref(v_tag_476_);
lean_inc_ref(v___x_525_);
lean_inc(v_cls_474_);
v_data_527_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_527_, 0, v_cls_474_);
lean_ctor_set(v_data_527_, 1, v___x_525_);
lean_ctor_set(v_data_527_, 2, v_tag_476_);
lean_ctor_set_float(v_data_527_, sizeof(void*)*3, v___x_526_);
lean_ctor_set_float(v_data_527_, sizeof(void*)*3 + 8, v___x_526_);
lean_ctor_set_uint8(v_data_527_, sizeof(void*)*3 + 16, v_collapsed_475_);
if (v___x_512_ == 0)
{
lean_dec_ref(v___x_525_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_dec_ref(v_tag_476_);
lean_dec(v_cls_474_);
v___y_493_ = v_m_523_;
v___y_494_ = v___y_514_;
v_data_495_ = v_data_527_;
goto v___jp_492_;
}
else
{
lean_object* v_data_528_; double v___x_529_; double v___x_530_; 
lean_dec_ref(v_data_527_);
v_data_528_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_528_, 0, v_cls_474_);
lean_ctor_set(v_data_528_, 1, v___x_525_);
lean_ctor_set(v_data_528_, 2, v_tag_476_);
v___x_529_ = lean_unbox_float(v_fst_506_);
lean_dec(v_fst_506_);
lean_ctor_set_float(v_data_528_, sizeof(void*)*3, v___x_529_);
v___x_530_ = lean_unbox_float(v_snd_507_);
lean_dec(v_snd_507_);
lean_ctor_set_float(v_data_528_, sizeof(void*)*3 + 8, v___x_530_);
lean_ctor_set_uint8(v_data_528_, sizeof(void*)*3 + 16, v_collapsed_475_);
v___y_493_ = v_m_523_;
v___y_494_ = v___y_514_;
v_data_495_ = v_data_528_;
goto v___jp_492_;
}
}
}
}
v___jp_533_:
{
lean_object* v_ref_534_; lean_object* v___x_535_; 
v_ref_534_ = lean_ctor_get(v___y_484_, 5);
lean_inc(v___y_485_);
lean_inc_ref(v___y_484_);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v_fst_487_);
v___x_535_ = lean_apply_6(v_msg_480_, v_fst_487_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, lean_box(0));
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v___y_514_ = v_ref_534_;
v_a_515_ = v_a_536_;
goto v___jp_513_;
}
else
{
lean_object* v___x_537_; 
lean_dec_ref(v___x_535_);
v___x_537_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4);
v___y_514_ = v_ref_534_;
v_a_515_ = v___x_537_;
goto v___jp_513_;
}
}
v___jp_538_:
{
if (v_clsEnabled_478_ == 0)
{
if (v___y_539_ == 0)
{
lean_object* v___x_540_; lean_object* v_traceState_541_; lean_object* v_env_542_; lean_object* v_nextMacroScope_543_; lean_object* v_ngen_544_; lean_object* v_auxDeclNGen_545_; lean_object* v_cache_546_; lean_object* v_messages_547_; lean_object* v_infoState_548_; lean_object* v_snapshotTasks_549_; lean_object* v_newDecls_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_569_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_del_object(v___x_490_);
lean_dec_ref(v_msg_480_);
lean_dec_ref(v_tag_476_);
lean_dec(v_cls_474_);
v___x_540_ = lean_st_ref_take(v___y_485_);
v_traceState_541_ = lean_ctor_get(v___x_540_, 4);
v_env_542_ = lean_ctor_get(v___x_540_, 0);
v_nextMacroScope_543_ = lean_ctor_get(v___x_540_, 1);
v_ngen_544_ = lean_ctor_get(v___x_540_, 2);
v_auxDeclNGen_545_ = lean_ctor_get(v___x_540_, 3);
v_cache_546_ = lean_ctor_get(v___x_540_, 5);
v_messages_547_ = lean_ctor_get(v___x_540_, 6);
v_infoState_548_ = lean_ctor_get(v___x_540_, 7);
v_snapshotTasks_549_ = lean_ctor_get(v___x_540_, 8);
v_newDecls_550_ = lean_ctor_get(v___x_540_, 9);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_569_ == 0)
{
v___x_552_ = v___x_540_;
v_isShared_553_ = v_isSharedCheck_569_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_newDecls_550_);
lean_inc(v_snapshotTasks_549_);
lean_inc(v_infoState_548_);
lean_inc(v_messages_547_);
lean_inc(v_cache_546_);
lean_inc(v_traceState_541_);
lean_inc(v_auxDeclNGen_545_);
lean_inc(v_ngen_544_);
lean_inc(v_nextMacroScope_543_);
lean_inc(v_env_542_);
lean_dec(v___x_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_569_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint64_t v_tid_554_; lean_object* v_traces_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_568_; 
v_tid_554_ = lean_ctor_get_uint64(v_traceState_541_, sizeof(void*)*1);
v_traces_555_ = lean_ctor_get(v_traceState_541_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_traceState_541_);
if (v_isSharedCheck_568_ == 0)
{
v___x_557_ = v_traceState_541_;
v_isShared_558_ = v_isSharedCheck_568_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_traces_555_);
lean_dec(v_traceState_541_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_568_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_479_, v_traces_555_);
lean_dec_ref(v_traces_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_559_);
lean_ctor_set_uint64(v_reuseFailAlloc_567_, sizeof(void*)*1, v_tid_554_);
v___x_561_ = v_reuseFailAlloc_567_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 4, v___x_561_);
v___x_563_ = v___x_552_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_env_542_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_nextMacroScope_543_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_ngen_544_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_auxDeclNGen_545_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_566_, 5, v_cache_546_);
lean_ctor_set(v_reuseFailAlloc_566_, 6, v_messages_547_);
lean_ctor_set(v_reuseFailAlloc_566_, 7, v_infoState_548_);
lean_ctor_set(v_reuseFailAlloc_566_, 8, v_snapshotTasks_549_);
lean_ctor_set(v_reuseFailAlloc_566_, 9, v_newDecls_550_);
v___x_563_ = v_reuseFailAlloc_566_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_st_ref_set(v___y_485_, v___x_563_);
v___x_565_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_487_);
return v___x_565_;
}
}
}
}
}
else
{
goto v___jp_533_;
}
}
else
{
goto v___jp_533_;
}
}
v___jp_570_:
{
double v___x_572_; double v___x_573_; double v___x_574_; uint8_t v___x_575_; 
v___x_572_ = lean_unbox_float(v_snd_507_);
v___x_573_ = lean_unbox_float(v_fst_506_);
v___x_574_ = lean_float_sub(v___x_572_, v___x_573_);
v___x_575_ = lean_float_decLt(v___y_571_, v___x_574_);
v___y_539_ = v___x_575_;
goto v___jp_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_588_, lean_object* v_collapsed_589_, lean_object* v_tag_590_, lean_object* v_opts_591_, lean_object* v_clsEnabled_592_, lean_object* v_oldTraces_593_, lean_object* v_msg_594_, lean_object* v_resStartStop_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
uint8_t v_collapsed_boxed_601_; uint8_t v_clsEnabled_boxed_602_; lean_object* v_res_603_; 
v_collapsed_boxed_601_ = lean_unbox(v_collapsed_589_);
v_clsEnabled_boxed_602_ = lean_unbox(v_clsEnabled_592_);
v_res_603_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_588_, v_collapsed_boxed_601_, v_tag_590_, v_opts_591_, v_clsEnabled_boxed_602_, v_oldTraces_593_, v_msg_594_, v_resStartStop_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v_opts_591_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_x_606_);
return v___x_612_;
}
else
{
lean_object* v_head_613_; lean_object* v_tail_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_637_; 
v_head_613_ = lean_ctor_get(v_x_605_, 0);
v_tail_614_ = lean_ctor_get(v_x_605_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_637_ == 0)
{
v___x_616_ = v_x_605_;
v_isShared_617_ = v_isSharedCheck_637_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_tail_614_);
lean_inc(v_head_613_);
lean_dec(v_x_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_637_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; 
lean_inc(v_head_613_);
v___x_618_ = l_Lean_MVarId_inferInstance(v_head_613_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_dec_ref(v___x_618_);
lean_del_object(v___x_616_);
lean_dec(v_head_613_);
v_x_605_ = v_tail_614_;
goto _start;
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_636_; 
v_a_620_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_636_ == 0)
{
v___x_622_ = v___x_618_;
v_isShared_623_ = v_isSharedCheck_636_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_618_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_636_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v___y_625_; uint8_t v___x_634_; 
v___x_634_ = l_Lean_Exception_isInterrupt(v_a_620_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
lean_inc(v_a_620_);
v___x_635_ = l_Lean_Exception_isRuntime(v_a_620_);
v___y_625_ = v___x_635_;
goto v___jp_624_;
}
else
{
v___y_625_ = v___x_634_;
goto v___jp_624_;
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
lean_del_object(v___x_622_);
lean_dec(v_a_620_);
if (v___x_604_ == 0)
{
lean_del_object(v___x_616_);
lean_dec(v_head_613_);
v_x_605_ = v_tail_614_;
goto _start;
}
else
{
lean_object* v___x_628_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_x_606_);
v___x_628_ = v___x_616_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_head_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_x_606_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_x_605_ = v_tail_614_;
v_x_606_ = v___x_628_;
goto _start;
}
}
}
else
{
lean_object* v___x_632_; 
lean_del_object(v___x_616_);
lean_dec(v_tail_614_);
lean_dec(v_head_613_);
lean_dec(v_x_606_);
if (v_isShared_623_ == 0)
{
v___x_632_ = v___x_622_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_620_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
uint8_t v___x_14687__boxed_646_; lean_object* v_res_647_; 
v___x_14687__boxed_646_ = lean_unbox(v___x_638_);
v_res_647_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14687__boxed_646_, v_x_639_, v_x_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_x_650_);
return v___x_656_;
}
else
{
lean_object* v_head_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_681_; 
v_head_657_ = lean_ctor_get(v_x_649_, 0);
v_tail_658_ = lean_ctor_get(v_x_649_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_681_ == 0)
{
v___x_660_ = v_x_649_;
v_isShared_661_ = v_isSharedCheck_681_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_head_657_);
lean_dec(v_x_649_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_681_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_667_; 
lean_inc(v_head_657_);
v___x_667_ = l_Lean_MVarId_inferInstance(v_head_657_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref(v___x_667_);
if (v___x_648_ == 0)
{
lean_del_object(v___x_660_);
lean_dec(v_head_657_);
v_x_649_ = v_tail_658_;
goto _start;
}
else
{
goto v___jp_662_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_680_; 
v_a_669_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_680_ == 0)
{
v___x_671_ = v___x_667_;
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
uint8_t v___y_674_; uint8_t v___x_678_; 
v___x_678_ = l_Lean_Exception_isInterrupt(v_a_669_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
lean_inc(v_a_669_);
v___x_679_ = l_Lean_Exception_isRuntime(v_a_669_);
v___y_674_ = v___x_679_;
goto v___jp_673_;
}
else
{
v___y_674_ = v___x_678_;
goto v___jp_673_;
}
v___jp_673_:
{
if (v___y_674_ == 0)
{
lean_del_object(v___x_671_);
lean_dec(v_a_669_);
goto v___jp_662_;
}
else
{
lean_object* v___x_676_; 
lean_del_object(v___x_660_);
lean_dec(v_tail_658_);
lean_dec(v_head_657_);
lean_dec(v_x_650_);
if (v_isShared_672_ == 0)
{
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_669_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
v___jp_662_:
{
lean_object* v___x_664_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_x_650_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_head_657_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_x_650_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v_x_649_ = v_tail_658_;
v_x_650_ = v___x_664_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_14764__boxed_690_; lean_object* v_res_691_; 
v___x_14764__boxed_690_ = lean_unbox(v___x_682_);
v_res_691_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14764__boxed_690_, v_x_683_, v_x_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_691_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_695_; double v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(1000000000u);
v___x_696_ = lean_float_of_nat(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_697_, lean_object* v_g_698_, lean_object* v_e_699_, lean_object* v_cfg_700_, lean_object* v___x_701_, lean_object* v___x_702_, uint8_t v___x_703_, lean_object* v___x_704_, lean_object* v___f_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_options_711_; uint8_t v_hasTrace_712_; 
v_options_711_ = lean_ctor_get(v___y_708_, 2);
v_hasTrace_712_ = lean_ctor_get_uint8(v_options_711_, sizeof(void*)*1);
if (v_hasTrace_712_ == 0)
{
lean_object* v___x_713_; uint8_t v_foApprox_714_; uint8_t v_ctxApprox_715_; uint8_t v_quasiPatternApprox_716_; uint8_t v_constApprox_717_; uint8_t v_isDefEqStuckEx_718_; uint8_t v_unificationHints_719_; uint8_t v_proofIrrelevance_720_; uint8_t v_assignSyntheticOpaque_721_; uint8_t v_offsetCnstrs_722_; uint8_t v_etaStruct_723_; uint8_t v_univApprox_724_; uint8_t v_iota_725_; uint8_t v_beta_726_; uint8_t v_proj_727_; uint8_t v_zeta_728_; uint8_t v_zetaDelta_729_; uint8_t v_zetaUnused_730_; uint8_t v_zetaHave_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_769_; 
lean_dec_ref(v___f_705_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_702_);
v___x_713_ = l_Lean_Meta_Context_config(v___y_706_);
v_foApprox_714_ = lean_ctor_get_uint8(v___x_713_, 0);
v_ctxApprox_715_ = lean_ctor_get_uint8(v___x_713_, 1);
v_quasiPatternApprox_716_ = lean_ctor_get_uint8(v___x_713_, 2);
v_constApprox_717_ = lean_ctor_get_uint8(v___x_713_, 3);
v_isDefEqStuckEx_718_ = lean_ctor_get_uint8(v___x_713_, 4);
v_unificationHints_719_ = lean_ctor_get_uint8(v___x_713_, 5);
v_proofIrrelevance_720_ = lean_ctor_get_uint8(v___x_713_, 6);
v_assignSyntheticOpaque_721_ = lean_ctor_get_uint8(v___x_713_, 7);
v_offsetCnstrs_722_ = lean_ctor_get_uint8(v___x_713_, 8);
v_etaStruct_723_ = lean_ctor_get_uint8(v___x_713_, 10);
v_univApprox_724_ = lean_ctor_get_uint8(v___x_713_, 11);
v_iota_725_ = lean_ctor_get_uint8(v___x_713_, 12);
v_beta_726_ = lean_ctor_get_uint8(v___x_713_, 13);
v_proj_727_ = lean_ctor_get_uint8(v___x_713_, 14);
v_zeta_728_ = lean_ctor_get_uint8(v___x_713_, 15);
v_zetaDelta_729_ = lean_ctor_get_uint8(v___x_713_, 16);
v_zetaUnused_730_ = lean_ctor_get_uint8(v___x_713_, 17);
v_zetaHave_731_ = lean_ctor_get_uint8(v___x_713_, 18);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_769_ == 0)
{
v___x_733_ = v___x_713_;
v_isShared_734_ = v_isSharedCheck_769_;
goto v_resetjp_732_;
}
else
{
lean_dec(v___x_713_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_769_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
uint8_t v_trackZetaDelta_735_; lean_object* v_zetaDeltaSet_736_; lean_object* v_lctx_737_; lean_object* v_localInstances_738_; lean_object* v_defEqCtx_x3f_739_; lean_object* v_synthPendingDepth_740_; lean_object* v_canUnfold_x3f_741_; uint8_t v_univApprox_742_; uint8_t v_inTypeClassResolution_743_; uint8_t v_cacheInferType_744_; lean_object* v_config_746_; 
v_trackZetaDelta_735_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7);
v_zetaDeltaSet_736_ = lean_ctor_get(v___y_706_, 1);
v_lctx_737_ = lean_ctor_get(v___y_706_, 2);
v_localInstances_738_ = lean_ctor_get(v___y_706_, 3);
v_defEqCtx_x3f_739_ = lean_ctor_get(v___y_706_, 4);
v_synthPendingDepth_740_ = lean_ctor_get(v___y_706_, 5);
v_canUnfold_x3f_741_ = lean_ctor_get(v___y_706_, 6);
v_univApprox_742_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_743_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 2);
v_cacheInferType_744_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 3);
if (v_isShared_734_ == 0)
{
v_config_746_ = v___x_733_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 0, v_foApprox_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 1, v_ctxApprox_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 2, v_quasiPatternApprox_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 3, v_constApprox_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 4, v_isDefEqStuckEx_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 5, v_unificationHints_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 6, v_proofIrrelevance_720_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 7, v_assignSyntheticOpaque_721_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 8, v_offsetCnstrs_722_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 10, v_etaStruct_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 11, v_univApprox_724_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 12, v_iota_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 13, v_beta_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 14, v_proj_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 15, v_zeta_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 16, v_zetaDelta_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 17, v_zetaUnused_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_768_, 18, v_zetaHave_731_);
v_config_746_ = v_reuseFailAlloc_768_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v_key_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_ctor_set_uint8(v_config_746_, 9, v_transparency_697_);
v___x_747_ = l_Lean_Meta_Context_configKey(v___y_706_);
v___x_748_ = 2ULL;
v___x_749_ = lean_uint64_shift_right(v___x_747_, v___x_748_);
v___x_750_ = lean_uint64_shift_left(v___x_749_, v___x_748_);
v___x_751_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_697_);
v_key_752_ = lean_uint64_lor(v___x_750_, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_753_, 0, v_config_746_);
lean_ctor_set_uint64(v___x_753_, sizeof(void*)*1, v_key_752_);
lean_inc(v_canUnfold_x3f_741_);
lean_inc(v_synthPendingDepth_740_);
lean_inc(v_defEqCtx_x3f_739_);
lean_inc_ref(v_localInstances_738_);
lean_inc_ref(v_lctx_737_);
lean_inc(v_zetaDeltaSet_736_);
v___x_754_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v_zetaDeltaSet_736_);
lean_ctor_set(v___x_754_, 2, v_lctx_737_);
lean_ctor_set(v___x_754_, 3, v_localInstances_738_);
lean_ctor_set(v___x_754_, 4, v_defEqCtx_x3f_739_);
lean_ctor_set(v___x_754_, 5, v_synthPendingDepth_740_);
lean_ctor_set(v___x_754_, 6, v_canUnfold_x3f_741_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*7, v_trackZetaDelta_735_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*7 + 1, v_univApprox_742_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*7 + 2, v_inTypeClassResolution_743_);
lean_ctor_set_uint8(v___x_754_, sizeof(void*)*7 + 3, v_cacheInferType_744_);
v___x_755_ = l_Lean_MVarId_apply(v_g_698_, v_e_699_, v_cfg_700_, v___x_701_, v___x_754_, v___y_707_, v___y_708_, v___y_709_);
lean_dec_ref(v___x_754_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_755_);
v___x_757_ = lean_box(0);
v___x_758_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_712_, v_a_756_, v___x_757_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_767_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = l_List_reverse___redArg(v_a_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
else
{
return v___x_758_;
}
}
else
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v_a_777_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v_a_792_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v_a_810_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v_a_822_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; 
v_inheritedTraceOptions_770_ = lean_ctor_get(v___y_708_, 13);
v___x_771_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_702_);
v___x_772_ = l_Lean_Name_append(v___x_771_, v___x_702_);
v___x_773_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_770_, v_options_711_, v___x_772_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = l_Lean_trace_profiler;
v___x_945_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_711_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v_foApprox_947_; uint8_t v_ctxApprox_948_; uint8_t v_quasiPatternApprox_949_; uint8_t v_constApprox_950_; uint8_t v_isDefEqStuckEx_951_; uint8_t v_unificationHints_952_; uint8_t v_proofIrrelevance_953_; uint8_t v_assignSyntheticOpaque_954_; uint8_t v_offsetCnstrs_955_; uint8_t v_etaStruct_956_; uint8_t v_univApprox_957_; uint8_t v_iota_958_; uint8_t v_beta_959_; uint8_t v_proj_960_; uint8_t v_zeta_961_; uint8_t v_zetaDelta_962_; uint8_t v_zetaUnused_963_; uint8_t v_zetaHave_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___f_705_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_702_);
v___x_946_ = l_Lean_Meta_Context_config(v___y_706_);
v_foApprox_947_ = lean_ctor_get_uint8(v___x_946_, 0);
v_ctxApprox_948_ = lean_ctor_get_uint8(v___x_946_, 1);
v_quasiPatternApprox_949_ = lean_ctor_get_uint8(v___x_946_, 2);
v_constApprox_950_ = lean_ctor_get_uint8(v___x_946_, 3);
v_isDefEqStuckEx_951_ = lean_ctor_get_uint8(v___x_946_, 4);
v_unificationHints_952_ = lean_ctor_get_uint8(v___x_946_, 5);
v_proofIrrelevance_953_ = lean_ctor_get_uint8(v___x_946_, 6);
v_assignSyntheticOpaque_954_ = lean_ctor_get_uint8(v___x_946_, 7);
v_offsetCnstrs_955_ = lean_ctor_get_uint8(v___x_946_, 8);
v_etaStruct_956_ = lean_ctor_get_uint8(v___x_946_, 10);
v_univApprox_957_ = lean_ctor_get_uint8(v___x_946_, 11);
v_iota_958_ = lean_ctor_get_uint8(v___x_946_, 12);
v_beta_959_ = lean_ctor_get_uint8(v___x_946_, 13);
v_proj_960_ = lean_ctor_get_uint8(v___x_946_, 14);
v_zeta_961_ = lean_ctor_get_uint8(v___x_946_, 15);
v_zetaDelta_962_ = lean_ctor_get_uint8(v___x_946_, 16);
v_zetaUnused_963_ = lean_ctor_get_uint8(v___x_946_, 17);
v_zetaHave_964_ = lean_ctor_get_uint8(v___x_946_, 18);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_966_ = v___x_946_;
v_isShared_967_ = v_isSharedCheck_1002_;
goto v_resetjp_965_;
}
else
{
lean_dec(v___x_946_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1002_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v_trackZetaDelta_968_; lean_object* v_zetaDeltaSet_969_; lean_object* v_lctx_970_; lean_object* v_localInstances_971_; lean_object* v_defEqCtx_x3f_972_; lean_object* v_synthPendingDepth_973_; lean_object* v_canUnfold_x3f_974_; uint8_t v_univApprox_975_; uint8_t v_inTypeClassResolution_976_; uint8_t v_cacheInferType_977_; lean_object* v_config_979_; 
v_trackZetaDelta_968_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7);
v_zetaDeltaSet_969_ = lean_ctor_get(v___y_706_, 1);
v_lctx_970_ = lean_ctor_get(v___y_706_, 2);
v_localInstances_971_ = lean_ctor_get(v___y_706_, 3);
v_defEqCtx_x3f_972_ = lean_ctor_get(v___y_706_, 4);
v_synthPendingDepth_973_ = lean_ctor_get(v___y_706_, 5);
v_canUnfold_x3f_974_ = lean_ctor_get(v___y_706_, 6);
v_univApprox_975_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_976_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 2);
v_cacheInferType_977_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 3);
if (v_isShared_967_ == 0)
{
v_config_979_ = v___x_966_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 0, v_foApprox_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 1, v_ctxApprox_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 2, v_quasiPatternApprox_949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 3, v_constApprox_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 4, v_isDefEqStuckEx_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 5, v_unificationHints_952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 6, v_proofIrrelevance_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 7, v_assignSyntheticOpaque_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 8, v_offsetCnstrs_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 10, v_etaStruct_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 11, v_univApprox_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 12, v_iota_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 13, v_beta_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 14, v_proj_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 15, v_zeta_961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 16, v_zetaDelta_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 17, v_zetaUnused_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, 18, v_zetaHave_964_);
v_config_979_ = v_reuseFailAlloc_1001_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
uint64_t v___x_980_; uint64_t v___x_981_; uint64_t v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; uint64_t v_key_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_ctor_set_uint8(v_config_979_, 9, v_transparency_697_);
v___x_980_ = l_Lean_Meta_Context_configKey(v___y_706_);
v___x_981_ = 2ULL;
v___x_982_ = lean_uint64_shift_right(v___x_980_, v___x_981_);
v___x_983_ = lean_uint64_shift_left(v___x_982_, v___x_981_);
v___x_984_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_697_);
v_key_985_ = lean_uint64_lor(v___x_983_, v___x_984_);
v___x_986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_986_, 0, v_config_979_);
lean_ctor_set_uint64(v___x_986_, sizeof(void*)*1, v_key_985_);
lean_inc(v_canUnfold_x3f_974_);
lean_inc(v_synthPendingDepth_973_);
lean_inc(v_defEqCtx_x3f_972_);
lean_inc_ref(v_localInstances_971_);
lean_inc_ref(v_lctx_970_);
lean_inc(v_zetaDeltaSet_969_);
v___x_987_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_zetaDeltaSet_969_);
lean_ctor_set(v___x_987_, 2, v_lctx_970_);
lean_ctor_set(v___x_987_, 3, v_localInstances_971_);
lean_ctor_set(v___x_987_, 4, v_defEqCtx_x3f_972_);
lean_ctor_set(v___x_987_, 5, v_synthPendingDepth_973_);
lean_ctor_set(v___x_987_, 6, v_canUnfold_x3f_974_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*7, v_trackZetaDelta_968_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*7 + 1, v_univApprox_975_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*7 + 2, v_inTypeClassResolution_976_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*7 + 3, v_cacheInferType_977_);
v___x_988_ = l_Lean_MVarId_apply(v_g_698_, v_e_699_, v_cfg_700_, v___x_701_, v___x_987_, v___y_707_, v___y_708_, v___y_709_);
lean_dec_ref(v___x_987_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref(v___x_988_);
v___x_990_ = lean_box(0);
v___x_991_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_945_, v_hasTrace_712_, v_a_989_, v___x_990_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1000_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1000_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = l_List_reverse___redArg(v_a_992_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
return v___x_991_;
}
}
else
{
return v___x_988_;
}
}
}
}
else
{
goto v___jp_837_;
}
}
else
{
goto v___jp_837_;
}
v___jp_774_:
{
lean_object* v___x_778_; double v___x_779_; double v___x_780_; double v___x_781_; double v___x_782_; double v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_778_ = lean_io_mono_nanos_now();
v___x_779_ = lean_float_of_nat(v___y_776_);
v___x_780_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_781_ = lean_float_div(v___x_779_, v___x_780_);
v___x_782_ = lean_float_of_nat(v___x_778_);
v___x_783_ = lean_float_div(v___x_782_, v___x_780_);
v___x_784_ = lean_box_float(v___x_781_);
v___x_785_ = lean_box_float(v___x_783_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_777_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_702_, v___x_703_, v___x_704_, v_options_711_, v___x_773_, v___y_775_, v___f_705_, v___x_787_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_788_;
}
v___jp_789_:
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v_a_792_);
v___y_775_ = v___y_790_;
v___y_776_ = v___y_791_;
v_a_777_ = v___x_793_;
goto v___jp_774_;
}
v___jp_794_:
{
if (lean_obj_tag(v___y_797_) == 0)
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___y_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___y_797_);
v___y_790_ = v___y_795_;
v___y_791_ = v___y_796_;
v_a_792_ = v_a_798_;
goto v___jp_789_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___y_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___y_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___y_797_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___y_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 0);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_775_ = v___y_795_;
v___y_776_ = v___y_796_;
v_a_777_ = v___x_804_;
goto v___jp_774_;
}
}
}
}
v___jp_807_:
{
lean_object* v___x_811_; double v___x_812_; double v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_811_ = lean_io_get_num_heartbeats();
v___x_812_ = lean_float_of_nat(v___y_809_);
v___x_813_ = lean_float_of_nat(v___x_811_);
v___x_814_ = lean_box_float(v___x_812_);
v___x_815_ = lean_box_float(v___x_813_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v_a_810_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_702_, v___x_703_, v___x_704_, v_options_711_, v___x_773_, v___y_808_, v___f_705_, v___x_817_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_818_;
}
v___jp_819_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_a_822_);
v___y_808_ = v___y_820_;
v___y_809_ = v___y_821_;
v_a_810_ = v___x_823_;
goto v___jp_807_;
}
v___jp_824_:
{
if (lean_obj_tag(v___y_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___y_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___y_827_);
v___y_820_ = v___y_825_;
v___y_821_ = v___y_826_;
v_a_822_ = v_a_828_;
goto v___jp_819_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___y_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___y_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___y_827_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___y_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v___y_808_ = v___y_825_;
v___y_809_ = v___y_826_;
v_a_810_ = v___x_834_;
goto v___jp_807_;
}
}
}
}
v___jp_837_:
{
lean_object* v___x_838_; lean_object* v_a_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_709_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v___x_840_ = l_Lean_trace_profiler_useHeartbeats;
v___x_841_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_711_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v_foApprox_844_; uint8_t v_ctxApprox_845_; uint8_t v_quasiPatternApprox_846_; uint8_t v_constApprox_847_; uint8_t v_isDefEqStuckEx_848_; uint8_t v_unificationHints_849_; uint8_t v_proofIrrelevance_850_; uint8_t v_assignSyntheticOpaque_851_; uint8_t v_offsetCnstrs_852_; uint8_t v_etaStruct_853_; uint8_t v_univApprox_854_; uint8_t v_iota_855_; uint8_t v_beta_856_; uint8_t v_proj_857_; uint8_t v_zeta_858_; uint8_t v_zetaDelta_859_; uint8_t v_zetaUnused_860_; uint8_t v_zetaHave_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_892_; 
v___x_842_ = lean_io_mono_nanos_now();
v___x_843_ = l_Lean_Meta_Context_config(v___y_706_);
v_foApprox_844_ = lean_ctor_get_uint8(v___x_843_, 0);
v_ctxApprox_845_ = lean_ctor_get_uint8(v___x_843_, 1);
v_quasiPatternApprox_846_ = lean_ctor_get_uint8(v___x_843_, 2);
v_constApprox_847_ = lean_ctor_get_uint8(v___x_843_, 3);
v_isDefEqStuckEx_848_ = lean_ctor_get_uint8(v___x_843_, 4);
v_unificationHints_849_ = lean_ctor_get_uint8(v___x_843_, 5);
v_proofIrrelevance_850_ = lean_ctor_get_uint8(v___x_843_, 6);
v_assignSyntheticOpaque_851_ = lean_ctor_get_uint8(v___x_843_, 7);
v_offsetCnstrs_852_ = lean_ctor_get_uint8(v___x_843_, 8);
v_etaStruct_853_ = lean_ctor_get_uint8(v___x_843_, 10);
v_univApprox_854_ = lean_ctor_get_uint8(v___x_843_, 11);
v_iota_855_ = lean_ctor_get_uint8(v___x_843_, 12);
v_beta_856_ = lean_ctor_get_uint8(v___x_843_, 13);
v_proj_857_ = lean_ctor_get_uint8(v___x_843_, 14);
v_zeta_858_ = lean_ctor_get_uint8(v___x_843_, 15);
v_zetaDelta_859_ = lean_ctor_get_uint8(v___x_843_, 16);
v_zetaUnused_860_ = lean_ctor_get_uint8(v___x_843_, 17);
v_zetaHave_861_ = lean_ctor_get_uint8(v___x_843_, 18);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_892_ == 0)
{
v___x_863_ = v___x_843_;
v_isShared_864_ = v_isSharedCheck_892_;
goto v_resetjp_862_;
}
else
{
lean_dec(v___x_843_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_892_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v_trackZetaDelta_865_; lean_object* v_zetaDeltaSet_866_; lean_object* v_lctx_867_; lean_object* v_localInstances_868_; lean_object* v_defEqCtx_x3f_869_; lean_object* v_synthPendingDepth_870_; lean_object* v_canUnfold_x3f_871_; uint8_t v_univApprox_872_; uint8_t v_inTypeClassResolution_873_; uint8_t v_cacheInferType_874_; lean_object* v_config_876_; 
v_trackZetaDelta_865_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7);
v_zetaDeltaSet_866_ = lean_ctor_get(v___y_706_, 1);
v_lctx_867_ = lean_ctor_get(v___y_706_, 2);
v_localInstances_868_ = lean_ctor_get(v___y_706_, 3);
v_defEqCtx_x3f_869_ = lean_ctor_get(v___y_706_, 4);
v_synthPendingDepth_870_ = lean_ctor_get(v___y_706_, 5);
v_canUnfold_x3f_871_ = lean_ctor_get(v___y_706_, 6);
v_univApprox_872_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_873_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 2);
v_cacheInferType_874_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 3);
if (v_isShared_864_ == 0)
{
v_config_876_ = v___x_863_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 0, v_foApprox_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 1, v_ctxApprox_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 2, v_quasiPatternApprox_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 3, v_constApprox_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 4, v_isDefEqStuckEx_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 5, v_unificationHints_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 6, v_proofIrrelevance_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 7, v_assignSyntheticOpaque_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 8, v_offsetCnstrs_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 10, v_etaStruct_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 11, v_univApprox_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 12, v_iota_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 13, v_beta_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 14, v_proj_857_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 15, v_zeta_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 16, v_zetaDelta_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 17, v_zetaUnused_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, 18, v_zetaHave_861_);
v_config_876_ = v_reuseFailAlloc_891_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v_key_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_ctor_set_uint8(v_config_876_, 9, v_transparency_697_);
v___x_877_ = l_Lean_Meta_Context_configKey(v___y_706_);
v___x_878_ = 2ULL;
v___x_879_ = lean_uint64_shift_right(v___x_877_, v___x_878_);
v___x_880_ = lean_uint64_shift_left(v___x_879_, v___x_878_);
v___x_881_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_697_);
v_key_882_ = lean_uint64_lor(v___x_880_, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_883_, 0, v_config_876_);
lean_ctor_set_uint64(v___x_883_, sizeof(void*)*1, v_key_882_);
lean_inc(v_canUnfold_x3f_871_);
lean_inc(v_synthPendingDepth_870_);
lean_inc(v_defEqCtx_x3f_869_);
lean_inc_ref(v_localInstances_868_);
lean_inc_ref(v_lctx_867_);
lean_inc(v_zetaDeltaSet_866_);
v___x_884_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_zetaDeltaSet_866_);
lean_ctor_set(v___x_884_, 2, v_lctx_867_);
lean_ctor_set(v___x_884_, 3, v_localInstances_868_);
lean_ctor_set(v___x_884_, 4, v_defEqCtx_x3f_869_);
lean_ctor_set(v___x_884_, 5, v_synthPendingDepth_870_);
lean_ctor_set(v___x_884_, 6, v_canUnfold_x3f_871_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7, v_trackZetaDelta_865_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7 + 1, v_univApprox_872_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7 + 2, v_inTypeClassResolution_873_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*7 + 3, v_cacheInferType_874_);
v___x_885_ = l_Lean_MVarId_apply(v_g_698_, v_e_699_, v_cfg_700_, v___x_701_, v___x_884_, v___y_707_, v___y_708_, v___y_709_);
lean_dec_ref(v___x_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v___x_887_ = lean_box(0);
v___x_888_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_841_, v_hasTrace_712_, v_a_886_, v___x_887_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
v___x_890_ = l_List_reverse___redArg(v_a_889_);
v___y_790_ = v_a_839_;
v___y_791_ = v___x_842_;
v_a_792_ = v___x_890_;
goto v___jp_789_;
}
else
{
v___y_795_ = v_a_839_;
v___y_796_ = v___x_842_;
v___y_797_ = v___x_888_;
goto v___jp_794_;
}
}
else
{
v___y_795_ = v_a_839_;
v___y_796_ = v___x_842_;
v___y_797_ = v___x_885_;
goto v___jp_794_;
}
}
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v_foApprox_895_; uint8_t v_ctxApprox_896_; uint8_t v_quasiPatternApprox_897_; uint8_t v_constApprox_898_; uint8_t v_isDefEqStuckEx_899_; uint8_t v_unificationHints_900_; uint8_t v_proofIrrelevance_901_; uint8_t v_assignSyntheticOpaque_902_; uint8_t v_offsetCnstrs_903_; uint8_t v_etaStruct_904_; uint8_t v_univApprox_905_; uint8_t v_iota_906_; uint8_t v_beta_907_; uint8_t v_proj_908_; uint8_t v_zeta_909_; uint8_t v_zetaDelta_910_; uint8_t v_zetaUnused_911_; uint8_t v_zetaHave_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_943_; 
v___x_893_ = lean_io_get_num_heartbeats();
v___x_894_ = l_Lean_Meta_Context_config(v___y_706_);
v_foApprox_895_ = lean_ctor_get_uint8(v___x_894_, 0);
v_ctxApprox_896_ = lean_ctor_get_uint8(v___x_894_, 1);
v_quasiPatternApprox_897_ = lean_ctor_get_uint8(v___x_894_, 2);
v_constApprox_898_ = lean_ctor_get_uint8(v___x_894_, 3);
v_isDefEqStuckEx_899_ = lean_ctor_get_uint8(v___x_894_, 4);
v_unificationHints_900_ = lean_ctor_get_uint8(v___x_894_, 5);
v_proofIrrelevance_901_ = lean_ctor_get_uint8(v___x_894_, 6);
v_assignSyntheticOpaque_902_ = lean_ctor_get_uint8(v___x_894_, 7);
v_offsetCnstrs_903_ = lean_ctor_get_uint8(v___x_894_, 8);
v_etaStruct_904_ = lean_ctor_get_uint8(v___x_894_, 10);
v_univApprox_905_ = lean_ctor_get_uint8(v___x_894_, 11);
v_iota_906_ = lean_ctor_get_uint8(v___x_894_, 12);
v_beta_907_ = lean_ctor_get_uint8(v___x_894_, 13);
v_proj_908_ = lean_ctor_get_uint8(v___x_894_, 14);
v_zeta_909_ = lean_ctor_get_uint8(v___x_894_, 15);
v_zetaDelta_910_ = lean_ctor_get_uint8(v___x_894_, 16);
v_zetaUnused_911_ = lean_ctor_get_uint8(v___x_894_, 17);
v_zetaHave_912_ = lean_ctor_get_uint8(v___x_894_, 18);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_943_ == 0)
{
v___x_914_ = v___x_894_;
v_isShared_915_ = v_isSharedCheck_943_;
goto v_resetjp_913_;
}
else
{
lean_dec(v___x_894_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_943_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
uint8_t v_trackZetaDelta_916_; lean_object* v_zetaDeltaSet_917_; lean_object* v_lctx_918_; lean_object* v_localInstances_919_; lean_object* v_defEqCtx_x3f_920_; lean_object* v_synthPendingDepth_921_; lean_object* v_canUnfold_x3f_922_; uint8_t v_univApprox_923_; uint8_t v_inTypeClassResolution_924_; uint8_t v_cacheInferType_925_; lean_object* v_config_927_; 
v_trackZetaDelta_916_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7);
v_zetaDeltaSet_917_ = lean_ctor_get(v___y_706_, 1);
v_lctx_918_ = lean_ctor_get(v___y_706_, 2);
v_localInstances_919_ = lean_ctor_get(v___y_706_, 3);
v_defEqCtx_x3f_920_ = lean_ctor_get(v___y_706_, 4);
v_synthPendingDepth_921_ = lean_ctor_get(v___y_706_, 5);
v_canUnfold_x3f_922_ = lean_ctor_get(v___y_706_, 6);
v_univApprox_923_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_924_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 2);
v_cacheInferType_925_ = lean_ctor_get_uint8(v___y_706_, sizeof(void*)*7 + 3);
if (v_isShared_915_ == 0)
{
v_config_927_ = v___x_914_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 0, v_foApprox_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 1, v_ctxApprox_896_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 2, v_quasiPatternApprox_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 3, v_constApprox_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 4, v_isDefEqStuckEx_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 5, v_unificationHints_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 6, v_proofIrrelevance_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 7, v_assignSyntheticOpaque_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 8, v_offsetCnstrs_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 10, v_etaStruct_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 11, v_univApprox_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 12, v_iota_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 13, v_beta_907_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 14, v_proj_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 15, v_zeta_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 16, v_zetaDelta_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 17, v_zetaUnused_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_942_, 18, v_zetaHave_912_);
v_config_927_ = v_reuseFailAlloc_942_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
uint64_t v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v___x_931_; uint64_t v___x_932_; uint64_t v_key_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_ctor_set_uint8(v_config_927_, 9, v_transparency_697_);
v___x_928_ = l_Lean_Meta_Context_configKey(v___y_706_);
v___x_929_ = 2ULL;
v___x_930_ = lean_uint64_shift_right(v___x_928_, v___x_929_);
v___x_931_ = lean_uint64_shift_left(v___x_930_, v___x_929_);
v___x_932_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_697_);
v_key_933_ = lean_uint64_lor(v___x_931_, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_934_, 0, v_config_927_);
lean_ctor_set_uint64(v___x_934_, sizeof(void*)*1, v_key_933_);
lean_inc(v_canUnfold_x3f_922_);
lean_inc(v_synthPendingDepth_921_);
lean_inc(v_defEqCtx_x3f_920_);
lean_inc_ref(v_localInstances_919_);
lean_inc_ref(v_lctx_918_);
lean_inc(v_zetaDeltaSet_917_);
v___x_935_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_zetaDeltaSet_917_);
lean_ctor_set(v___x_935_, 2, v_lctx_918_);
lean_ctor_set(v___x_935_, 3, v_localInstances_919_);
lean_ctor_set(v___x_935_, 4, v_defEqCtx_x3f_920_);
lean_ctor_set(v___x_935_, 5, v_synthPendingDepth_921_);
lean_ctor_set(v___x_935_, 6, v_canUnfold_x3f_922_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*7, v_trackZetaDelta_916_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*7 + 1, v_univApprox_923_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*7 + 2, v_inTypeClassResolution_924_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*7 + 3, v_cacheInferType_925_);
v___x_936_ = l_Lean_MVarId_apply(v_g_698_, v_e_699_, v_cfg_700_, v___x_701_, v___x_935_, v___y_707_, v___y_708_, v___y_709_);
lean_dec_ref(v___x_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = lean_box(0);
v___x_939_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_841_, v_a_937_, v___x_938_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_941_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref(v___x_939_);
v___x_941_ = l_List_reverse___redArg(v_a_940_);
v___y_820_ = v_a_839_;
v___y_821_ = v___x_893_;
v_a_822_ = v___x_941_;
goto v___jp_819_;
}
else
{
v___y_825_ = v_a_839_;
v___y_826_ = v___x_893_;
v___y_827_ = v___x_939_;
goto v___jp_824_;
}
}
else
{
v___y_825_ = v_a_839_;
v___y_826_ = v___x_893_;
v___y_827_ = v___x_936_;
goto v___jp_824_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_1003_, lean_object* v_g_1004_, lean_object* v_e_1005_, lean_object* v_cfg_1006_, lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___f_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v_transparency_boxed_1017_; uint8_t v___x_14852__boxed_1018_; lean_object* v_res_1019_; 
v_transparency_boxed_1017_ = lean_unbox(v_transparency_1003_);
v___x_14852__boxed_1018_ = lean_unbox(v___x_1009_);
v_res_1019_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_1017_, v_g_1004_, v_e_1005_, v_cfg_1006_, v___x_1007_, v___x_1008_, v___x_14852__boxed_1018_, v___x_1010_, v___f_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_1021_, lean_object* v_g_1022_, lean_object* v_cfg_1023_, lean_object* v_e_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; 
lean_inc_ref(v_e_1024_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1030_, 0, v_e_1024_);
v___x_1031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1032_ = lean_box(0);
v___x_1033_ = 1;
v___x_1034_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1035_ = lean_box(v_transparency_1021_);
v___x_1036_ = lean_box(v___x_1033_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1037_, 0, v___x_1035_);
lean_closure_set(v___f_1037_, 1, v_g_1022_);
lean_closure_set(v___f_1037_, 2, v_e_1024_);
lean_closure_set(v___f_1037_, 3, v_cfg_1023_);
lean_closure_set(v___f_1037_, 4, v___x_1032_);
lean_closure_set(v___f_1037_, 5, v___x_1031_);
lean_closure_set(v___f_1037_, 6, v___x_1036_);
lean_closure_set(v___f_1037_, 7, v___x_1034_);
lean_closure_set(v___f_1037_, 8, v___f_1030_);
v___x_1038_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_1037_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1039_, lean_object* v_g_1040_, lean_object* v_cfg_1041_, lean_object* v_e_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v_transparency_boxed_1048_; lean_object* v_res_1049_; 
v_transparency_boxed_1048_ = lean_unbox(v_transparency_1039_);
v_res_1049_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1048_, v_g_1040_, v_cfg_1041_, v_e_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1050_, uint8_t v_transparency_1051_, lean_object* v_lemmas_1052_, lean_object* v_g_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1052_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1068_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1062_ = lean_box(v_transparency_1051_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1063_, 0, v___x_1062_);
lean_closure_set(v___f_1063_, 1, v_g_1053_);
lean_closure_set(v___f_1063_, 2, v_cfg_1050_);
v___x_1064_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1064_, 0, lean_box(0));
lean_closure_set(v___x_1064_, 1, lean_box(0));
lean_closure_set(v___x_1064_, 2, v___f_1063_);
lean_closure_set(v___x_1064_, 3, v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1064_);
v___x_1066_ = v___x_1060_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_g_1053_);
lean_dec_ref(v_cfg_1050_);
v_a_1069_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1057_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1057_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1077_, lean_object* v_transparency_1078_, lean_object* v_lemmas_1079_, lean_object* v_g_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
uint8_t v_transparency_boxed_1084_; lean_object* v_res_1085_; 
v_transparency_boxed_1084_ = lean_unbox(v_transparency_1078_);
v_res_1085_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1077_, v_transparency_boxed_1084_, v_lemmas_1079_, v_g_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec(v_a_1081_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1086_, uint8_t v_transparency_1087_, lean_object* v_lemmas_1088_, lean_object* v_g_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1086_, v_transparency_1087_, v_lemmas_1088_, v_g_1089_, v_a_1091_, v_a_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1096_, lean_object* v_transparency_1097_, lean_object* v_lemmas_1098_, lean_object* v_g_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
uint8_t v_transparency_boxed_1105_; lean_object* v_res_1106_; 
v_transparency_boxed_1105_ = lean_unbox(v_transparency_1097_);
v_res_1106_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1096_, v_transparency_boxed_1105_, v_lemmas_1098_, v_g_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_00_u03b1_1107_, lean_object* v_x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_1108_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1115_, lean_object* v_x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_00_u03b1_1115_, v_x_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1123_, uint8_t v_transparency_1124_, lean_object* v_lemmas_1125_, lean_object* v_g_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1123_, v_transparency_1124_, v_lemmas_1125_, v_g_1126_, v_a_1128_, v_a_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = l_Lean_Meta_Iterator_head___redArg(v_a_1133_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1134_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1132_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1143_, lean_object* v_transparency_1144_, lean_object* v_lemmas_1145_, lean_object* v_g_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_transparency_boxed_1152_; lean_object* v_res_1153_; 
v_transparency_boxed_1152_ = lean_unbox(v_transparency_1144_);
v_res_1153_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1143_, v_transparency_boxed_1152_, v_lemmas_1145_, v_g_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1154_){
_start:
{
lean_object* v_toApplyRulesConfig_1155_; lean_object* v_toBacktrackConfig_1156_; 
v_toApplyRulesConfig_1155_ = lean_ctor_get(v_x_1154_, 0);
v_toBacktrackConfig_1156_ = lean_ctor_get(v_toApplyRulesConfig_1155_, 0);
lean_inc_ref(v_toBacktrackConfig_1156_);
return v_toBacktrackConfig_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1157_);
lean_dec_ref(v_x_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1161_, lean_object* v_discharge_1162_, lean_object* v_g_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v_g_1163_);
v___x_1169_ = lean_apply_6(v_test_1161_, v_g_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, lean_box(0));
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1180_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1180_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_unbox(v_a_1170_);
lean_dec(v_a_1170_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_del_object(v___x_1172_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
v___x_1175_ = lean_apply_6(v_discharge_1162_, v_g_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, lean_box(0));
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec(v_g_1163_);
lean_dec_ref(v_discharge_1162_);
v___x_1176_ = lean_box(0);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1176_);
v___x_1178_ = v___x_1172_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_g_1163_);
lean_dec_ref(v_discharge_1162_);
v_a_1181_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1169_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1169_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1189_, lean_object* v_discharge_1190_, lean_object* v_g_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1189_, v_discharge_1190_, v_g_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1198_, lean_object* v_test_1199_){
_start:
{
lean_object* v_toApplyRulesConfig_1200_; lean_object* v_toBacktrackConfig_1201_; uint8_t v_backtracking_1202_; uint8_t v_intro_1203_; uint8_t v_constructor_1204_; uint8_t v_suggestions_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1237_; 
v_toApplyRulesConfig_1200_ = lean_ctor_get(v_cfg_1198_, 0);
lean_inc_ref(v_toApplyRulesConfig_1200_);
v_toBacktrackConfig_1201_ = lean_ctor_get(v_toApplyRulesConfig_1200_, 0);
lean_inc_ref(v_toBacktrackConfig_1201_);
v_backtracking_1202_ = lean_ctor_get_uint8(v_cfg_1198_, sizeof(void*)*1);
v_intro_1203_ = lean_ctor_get_uint8(v_cfg_1198_, sizeof(void*)*1 + 1);
v_constructor_1204_ = lean_ctor_get_uint8(v_cfg_1198_, sizeof(void*)*1 + 2);
v_suggestions_1205_ = lean_ctor_get_uint8(v_cfg_1198_, sizeof(void*)*1 + 3);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_cfg_1198_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_cfg_1198_, 0);
lean_dec(v_unused_1238_);
v___x_1207_ = v_cfg_1198_;
v_isShared_1208_ = v_isSharedCheck_1237_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v_cfg_1198_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1237_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_toApplyConfig_1209_; uint8_t v_transparency_1210_; uint8_t v_symm_1211_; uint8_t v_exfalso_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1235_; 
v_toApplyConfig_1209_ = lean_ctor_get(v_toApplyRulesConfig_1200_, 1);
v_transparency_1210_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1200_, sizeof(void*)*2);
v_symm_1211_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1200_, sizeof(void*)*2 + 1);
v_exfalso_1212_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1200_, sizeof(void*)*2 + 2);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_toApplyRulesConfig_1200_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_toApplyRulesConfig_1200_, 0);
lean_dec(v_unused_1236_);
v___x_1214_ = v_toApplyRulesConfig_1200_;
v_isShared_1215_ = v_isSharedCheck_1235_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_toApplyConfig_1209_);
lean_dec(v_toApplyRulesConfig_1200_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1235_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_maxDepth_1216_; lean_object* v_proc_1217_; lean_object* v_suspend_1218_; lean_object* v_discharge_1219_; uint8_t v_commitIndependentGoals_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1234_; 
v_maxDepth_1216_ = lean_ctor_get(v_toBacktrackConfig_1201_, 0);
v_proc_1217_ = lean_ctor_get(v_toBacktrackConfig_1201_, 1);
v_suspend_1218_ = lean_ctor_get(v_toBacktrackConfig_1201_, 2);
v_discharge_1219_ = lean_ctor_get(v_toBacktrackConfig_1201_, 3);
v_commitIndependentGoals_1220_ = lean_ctor_get_uint8(v_toBacktrackConfig_1201_, sizeof(void*)*4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_toBacktrackConfig_1201_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1222_ = v_toBacktrackConfig_1201_;
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_discharge_1219_);
lean_inc(v_suspend_1218_);
lean_inc(v_proc_1217_);
lean_inc(v_maxDepth_1216_);
lean_dec(v_toBacktrackConfig_1201_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___f_1224_; lean_object* v___x_1226_; 
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1224_, 0, v_test_1199_);
lean_closure_set(v___f_1224_, 1, v_discharge_1219_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 3, v___f_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_maxDepth_1216_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_proc_1217_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_suspend_1218_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v___f_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1233_, sizeof(void*)*4, v_commitIndependentGoals_1220_);
v___x_1226_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1226_);
v___x_1228_ = v___x_1214_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_toApplyConfig_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, sizeof(void*)*2, v_transparency_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, sizeof(void*)*2 + 1, v_symm_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, sizeof(void*)*2 + 2, v_exfalso_1212_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1228_);
v___x_1230_ = v___x_1207_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*1, v_backtracking_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*1 + 1, v_intro_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*1 + 2, v_constructor_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*1 + 3, v_suggestions_1205_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1239_, lean_object* v_proc_1240_, lean_object* v_orig_1241_, lean_object* v_goals_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
if (lean_obj_tag(v_goals_1242_) == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref(v_proc_1240_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
v___x_1248_ = lean_apply_7(v_proc_1239_, v_orig_1241_, v_goals_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, lean_box(0));
return v___x_1248_;
}
else
{
lean_object* v_head_1249_; lean_object* v_tail_1250_; lean_object* v___x_1251_; 
v_head_1249_ = lean_ctor_get(v_goals_1242_, 0);
v_tail_1250_ = lean_ctor_get(v_goals_1242_, 1);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v_head_1249_);
v___x_1251_ = lean_apply_6(v_proc_1240_, v_head_1249_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, lean_box(0));
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1261_; 
lean_inc(v_tail_1250_);
lean_dec_ref(v_goals_1242_);
lean_dec(v_orig_1241_);
lean_dec_ref(v_proc_1239_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = l_List_appendTR___redArg(v_a_1252_, v_tail_1250_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1274_; 
v_a_1262_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1264_ = v___x_1251_;
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1251_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
uint8_t v___y_1267_; uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Exception_isInterrupt(v_a_1262_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
lean_inc(v_a_1262_);
v___x_1273_ = l_Lean_Exception_isRuntime(v_a_1262_);
v___y_1267_ = v___x_1273_;
goto v___jp_1266_;
}
else
{
v___y_1267_ = v___x_1272_;
goto v___jp_1266_;
}
v___jp_1266_:
{
if (v___y_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_del_object(v___x_1264_);
lean_dec(v_a_1262_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
v___x_1268_ = lean_apply_7(v_proc_1239_, v_orig_1241_, v_goals_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, lean_box(0));
return v___x_1268_;
}
else
{
lean_object* v___x_1270_; 
lean_dec_ref(v_goals_1242_);
lean_dec(v_orig_1241_);
lean_dec_ref(v_proc_1239_);
if (v_isShared_1265_ == 0)
{
v___x_1270_ = v___x_1264_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1262_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1275_, lean_object* v_proc_1276_, lean_object* v_orig_1277_, lean_object* v_goals_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1275_, v_proc_1276_, v_orig_1277_, v_goals_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1285_, lean_object* v_proc_1286_){
_start:
{
lean_object* v_toApplyRulesConfig_1287_; lean_object* v_toBacktrackConfig_1288_; uint8_t v_backtracking_1289_; uint8_t v_intro_1290_; uint8_t v_constructor_1291_; uint8_t v_suggestions_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1324_; 
v_toApplyRulesConfig_1287_ = lean_ctor_get(v_cfg_1285_, 0);
lean_inc_ref(v_toApplyRulesConfig_1287_);
v_toBacktrackConfig_1288_ = lean_ctor_get(v_toApplyRulesConfig_1287_, 0);
lean_inc_ref(v_toBacktrackConfig_1288_);
v_backtracking_1289_ = lean_ctor_get_uint8(v_cfg_1285_, sizeof(void*)*1);
v_intro_1290_ = lean_ctor_get_uint8(v_cfg_1285_, sizeof(void*)*1 + 1);
v_constructor_1291_ = lean_ctor_get_uint8(v_cfg_1285_, sizeof(void*)*1 + 2);
v_suggestions_1292_ = lean_ctor_get_uint8(v_cfg_1285_, sizeof(void*)*1 + 3);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_cfg_1285_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_cfg_1285_, 0);
lean_dec(v_unused_1325_);
v___x_1294_ = v_cfg_1285_;
v_isShared_1295_ = v_isSharedCheck_1324_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v_cfg_1285_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1324_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v_toApplyConfig_1296_; uint8_t v_transparency_1297_; uint8_t v_symm_1298_; uint8_t v_exfalso_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1322_; 
v_toApplyConfig_1296_ = lean_ctor_get(v_toApplyRulesConfig_1287_, 1);
v_transparency_1297_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1287_, sizeof(void*)*2);
v_symm_1298_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1287_, sizeof(void*)*2 + 1);
v_exfalso_1299_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1287_, sizeof(void*)*2 + 2);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_toApplyRulesConfig_1287_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_toApplyRulesConfig_1287_, 0);
lean_dec(v_unused_1323_);
v___x_1301_ = v_toApplyRulesConfig_1287_;
v_isShared_1302_ = v_isSharedCheck_1322_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_toApplyConfig_1296_);
lean_dec(v_toApplyRulesConfig_1287_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1322_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v_maxDepth_1303_; lean_object* v_proc_1304_; lean_object* v_suspend_1305_; lean_object* v_discharge_1306_; uint8_t v_commitIndependentGoals_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1321_; 
v_maxDepth_1303_ = lean_ctor_get(v_toBacktrackConfig_1288_, 0);
v_proc_1304_ = lean_ctor_get(v_toBacktrackConfig_1288_, 1);
v_suspend_1305_ = lean_ctor_get(v_toBacktrackConfig_1288_, 2);
v_discharge_1306_ = lean_ctor_get(v_toBacktrackConfig_1288_, 3);
v_commitIndependentGoals_1307_ = lean_ctor_get_uint8(v_toBacktrackConfig_1288_, sizeof(void*)*4);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_toBacktrackConfig_1288_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1309_ = v_toBacktrackConfig_1288_;
v_isShared_1310_ = v_isSharedCheck_1321_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_discharge_1306_);
lean_inc(v_suspend_1305_);
lean_inc(v_proc_1304_);
lean_inc(v_maxDepth_1303_);
lean_dec(v_toBacktrackConfig_1288_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1321_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___f_1311_; lean_object* v___x_1313_; 
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1311_, 0, v_proc_1304_);
lean_closure_set(v___f_1311_, 1, v_proc_1286_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___f_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_maxDepth_1303_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___f_1311_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_suspend_1305_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_discharge_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1320_, sizeof(void*)*4, v_commitIndependentGoals_1307_);
v___x_1313_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1313_);
v___x_1315_ = v___x_1301_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_toApplyConfig_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*2, v_transparency_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*2 + 1, v_symm_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*2 + 2, v_exfalso_1299_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1315_);
v___x_1317_ = v___x_1294_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1, v_backtracking_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1 + 1, v_intro_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1 + 2, v_constructor_1291_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*1 + 3, v_suggestions_1292_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = 1;
v___x_1333_ = l_Lean_Meta_intro1Core(v_g_1326_, v___x_1332_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1351_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1351_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1351_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_snd_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1349_; 
v_snd_1338_ = lean_ctor_get(v_a_1334_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_a_1334_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_a_1334_, 0);
lean_dec(v_unused_1350_);
v___x_1340_ = v_a_1334_;
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snd_1338_);
lean_dec(v_a_1334_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1342_ = lean_box(0);
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 1);
lean_ctor_set(v___x_1340_, 1, v___x_1342_);
lean_ctor_set(v___x_1340_, 0, v_snd_1338_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_snd_1338_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1344_);
v___x_1346_ = v___x_1336_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1333_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1333_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1368_){
_start:
{
lean_object* v___f_1369_; lean_object* v___x_1370_; 
v___f_1369_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1370_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1368_, v___f_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v_ks_1375_; lean_object* v_vs_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1400_; 
v_ks_1375_ = lean_ctor_get(v_x_1371_, 0);
v_vs_1376_ = lean_ctor_get(v_x_1371_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1371_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1378_ = v_x_1371_;
v_isShared_1379_ = v_isSharedCheck_1400_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_vs_1376_);
lean_inc(v_ks_1375_);
lean_dec(v_x_1371_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1400_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_array_get_size(v_ks_1375_);
v___x_1381_ = lean_nat_dec_lt(v_x_1372_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec(v_x_1372_);
v___x_1382_ = lean_array_push(v_ks_1375_, v_x_1373_);
v___x_1383_ = lean_array_push(v_vs_1376_, v_x_1374_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v___x_1383_);
lean_ctor_set(v___x_1378_, 0, v___x_1382_);
v___x_1385_ = v___x_1378_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
else
{
lean_object* v_k_x27_1387_; uint8_t v___x_1388_; 
v_k_x27_1387_ = lean_array_fget_borrowed(v_ks_1375_, v_x_1372_);
v___x_1388_ = l_Lean_instBEqMVarId_beq(v_x_1373_, v_k_x27_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; 
if (v_isShared_1379_ == 0)
{
v___x_1390_ = v___x_1378_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_ks_1375_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_vs_1376_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_x_1372_, v___x_1391_);
lean_dec(v_x_1372_);
v_x_1371_ = v___x_1390_;
v_x_1372_ = v___x_1392_;
goto _start;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = lean_array_fset(v_ks_1375_, v_x_1372_, v_x_1373_);
v___x_1396_ = lean_array_fset(v_vs_1376_, v_x_1372_, v_x_1374_);
lean_dec(v_x_1372_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v___x_1396_);
lean_ctor_set(v___x_1378_, 0, v___x_1395_);
v___x_1398_ = v___x_1378_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1401_, lean_object* v_k_1402_, lean_object* v_v_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1401_, v___x_1404_, v_k_1402_, v_v_1403_);
return v___x_1405_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1406_; size_t v___x_1407_; size_t v___x_1408_; 
v___x_1406_ = ((size_t)5ULL);
v___x_1407_ = ((size_t)1ULL);
v___x_1408_ = lean_usize_shift_left(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; 
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1411_ = lean_usize_sub(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1413_, size_t v_x_1414_, size_t v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v_es_1418_; size_t v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; lean_object* v_j_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_es_1418_ = lean_ctor_get(v_x_1413_, 0);
v___x_1419_ = ((size_t)5ULL);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1422_ = lean_usize_land(v_x_1414_, v___x_1421_);
v_j_1423_ = lean_usize_to_nat(v___x_1422_);
v___x_1424_ = lean_array_get_size(v_es_1418_);
v___x_1425_ = lean_nat_dec_lt(v_j_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_j_1423_);
lean_dec(v_x_1417_);
lean_dec(v_x_1416_);
return v_x_1413_;
}
else
{
lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1462_; 
lean_inc_ref(v_es_1418_);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_x_1413_, 0);
lean_dec(v_unused_1463_);
v___x_1427_ = v_x_1413_;
v_isShared_1428_ = v_isSharedCheck_1462_;
goto v_resetjp_1426_;
}
else
{
lean_dec(v_x_1413_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1462_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_v_1429_; lean_object* v___x_1430_; lean_object* v_xs_x27_1431_; lean_object* v___y_1433_; 
v_v_1429_ = lean_array_fget(v_es_1418_, v_j_1423_);
v___x_1430_ = lean_box(0);
v_xs_x27_1431_ = lean_array_fset(v_es_1418_, v_j_1423_, v___x_1430_);
switch(lean_obj_tag(v_v_1429_))
{
case 0:
{
lean_object* v_key_1438_; lean_object* v_val_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1449_; 
v_key_1438_ = lean_ctor_get(v_v_1429_, 0);
v_val_1439_ = lean_ctor_get(v_v_1429_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_v_1429_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1441_ = v_v_1429_;
v_isShared_1442_ = v_isSharedCheck_1449_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_val_1439_);
lean_inc(v_key_1438_);
lean_dec(v_v_1429_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1449_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_instBEqMVarId_beq(v_x_1416_, v_key_1438_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_del_object(v___x_1441_);
v___x_1444_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1438_, v_val_1439_, v_x_1416_, v_x_1417_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
v___y_1433_ = v___x_1445_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1447_; 
lean_dec(v_val_1439_);
lean_dec(v_key_1438_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v_x_1417_);
lean_ctor_set(v___x_1441_, 0, v_x_1416_);
v___x_1447_ = v___x_1441_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_x_1416_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_x_1417_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
v___y_1433_ = v___x_1447_;
goto v___jp_1432_;
}
}
}
}
case 1:
{
lean_object* v_node_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1460_; 
v_node_1450_ = lean_ctor_get(v_v_1429_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_v_1429_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1452_ = v_v_1429_;
v_isShared_1453_ = v_isSharedCheck_1460_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_node_1450_);
lean_dec(v_v_1429_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1460_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1454_ = lean_usize_shift_right(v_x_1414_, v___x_1419_);
v___x_1455_ = lean_usize_add(v_x_1415_, v___x_1420_);
v___x_1456_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1450_, v___x_1454_, v___x_1455_, v_x_1416_, v_x_1417_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1456_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
v___y_1433_ = v___x_1458_;
goto v___jp_1432_;
}
}
}
default: 
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_x_1416_);
lean_ctor_set(v___x_1461_, 1, v_x_1417_);
v___y_1433_ = v___x_1461_;
goto v___jp_1432_;
}
}
v___jp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_array_fset(v_xs_x27_1431_, v_j_1423_, v___y_1433_);
lean_dec(v_j_1423_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1434_);
v___x_1436_ = v___x_1427_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
else
{
lean_object* v_ks_1464_; lean_object* v_vs_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1485_; 
v_ks_1464_ = lean_ctor_get(v_x_1413_, 0);
v_vs_1465_ = lean_ctor_get(v_x_1413_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_x_1413_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1467_ = v_x_1413_;
v_isShared_1468_ = v_isSharedCheck_1485_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_vs_1465_);
lean_inc(v_ks_1464_);
lean_dec(v_x_1413_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1485_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_ks_1464_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_vs_1465_);
v___x_1470_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v_newNode_1471_; uint8_t v___y_1473_; size_t v___x_1479_; uint8_t v___x_1480_; 
v_newNode_1471_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1470_, v_x_1416_, v_x_1417_);
v___x_1479_ = ((size_t)7ULL);
v___x_1480_ = lean_usize_dec_le(v___x_1479_, v_x_1415_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1471_);
v___x_1482_ = lean_unsigned_to_nat(4u);
v___x_1483_ = lean_nat_dec_lt(v___x_1481_, v___x_1482_);
lean_dec(v___x_1481_);
v___y_1473_ = v___x_1483_;
goto v___jp_1472_;
}
else
{
v___y_1473_ = v___x_1480_;
goto v___jp_1472_;
}
v___jp_1472_:
{
if (v___y_1473_ == 0)
{
lean_object* v_ks_1474_; lean_object* v_vs_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_ks_1474_ = lean_ctor_get(v_newNode_1471_, 0);
lean_inc_ref(v_ks_1474_);
v_vs_1475_ = lean_ctor_get(v_newNode_1471_, 1);
lean_inc_ref(v_vs_1475_);
lean_dec_ref(v_newNode_1471_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1415_, v_ks_1474_, v_vs_1475_, v___x_1476_, v___x_1477_);
lean_dec_ref(v_vs_1475_);
lean_dec_ref(v_ks_1474_);
return v___x_1478_;
}
else
{
return v_newNode_1471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1486_, lean_object* v_keys_1487_, lean_object* v_vals_1488_, lean_object* v_i_1489_, lean_object* v_entries_1490_){
_start:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1491_ = lean_array_get_size(v_keys_1487_);
v___x_1492_ = lean_nat_dec_lt(v_i_1489_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec(v_i_1489_);
return v_entries_1490_;
}
else
{
lean_object* v_k_1493_; lean_object* v_v_1494_; uint64_t v___x_1495_; size_t v_h_1496_; size_t v___x_1497_; lean_object* v___x_1498_; size_t v___x_1499_; size_t v___x_1500_; size_t v___x_1501_; size_t v_h_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_k_1493_ = lean_array_fget_borrowed(v_keys_1487_, v_i_1489_);
v_v_1494_ = lean_array_fget_borrowed(v_vals_1488_, v_i_1489_);
v___x_1495_ = l_Lean_instHashableMVarId_hash(v_k_1493_);
v_h_1496_ = lean_uint64_to_usize(v___x_1495_);
v___x_1497_ = ((size_t)5ULL);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = ((size_t)1ULL);
v___x_1500_ = lean_usize_sub(v_depth_1486_, v___x_1499_);
v___x_1501_ = lean_usize_mul(v___x_1497_, v___x_1500_);
v_h_1502_ = lean_usize_shift_right(v_h_1496_, v___x_1501_);
v___x_1503_ = lean_nat_add(v_i_1489_, v___x_1498_);
lean_dec(v_i_1489_);
lean_inc(v_v_1494_);
lean_inc(v_k_1493_);
v___x_1504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1490_, v_h_1502_, v_depth_1486_, v_k_1493_, v_v_1494_);
v_i_1489_ = v___x_1503_;
v_entries_1490_ = v___x_1504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1506_, lean_object* v_keys_1507_, lean_object* v_vals_1508_, lean_object* v_i_1509_, lean_object* v_entries_1510_){
_start:
{
size_t v_depth_boxed_1511_; lean_object* v_res_1512_; 
v_depth_boxed_1511_ = lean_unbox_usize(v_depth_1506_);
lean_dec(v_depth_1506_);
v_res_1512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1511_, v_keys_1507_, v_vals_1508_, v_i_1509_, v_entries_1510_);
lean_dec_ref(v_vals_1508_);
lean_dec_ref(v_keys_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
size_t v_x_838__boxed_1518_; size_t v_x_839__boxed_1519_; lean_object* v_res_1520_; 
v_x_838__boxed_1518_ = lean_unbox_usize(v_x_1514_);
lean_dec(v_x_1514_);
v_x_839__boxed_1519_ = lean_unbox_usize(v_x_1515_);
lean_dec(v_x_1515_);
v_res_1520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1513_, v_x_838__boxed_1518_, v_x_839__boxed_1519_, v_x_1516_, v_x_1517_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
uint64_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = l_Lean_instHashableMVarId_hash(v_x_1522_);
v___x_1525_ = lean_uint64_to_usize(v___x_1524_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1521_, v___x_1525_, v___x_1526_, v_x_1522_, v_x_1523_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1528_, lean_object* v_val_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v_mctx_1533_; lean_object* v_cache_1534_; lean_object* v_zetaDeltaFVarIds_1535_; lean_object* v_postponed_1536_; lean_object* v_diag_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1565_; 
v___x_1532_ = lean_st_ref_take(v___y_1530_);
v_mctx_1533_ = lean_ctor_get(v___x_1532_, 0);
v_cache_1534_ = lean_ctor_get(v___x_1532_, 1);
v_zetaDeltaFVarIds_1535_ = lean_ctor_get(v___x_1532_, 2);
v_postponed_1536_ = lean_ctor_get(v___x_1532_, 3);
v_diag_1537_ = lean_ctor_get(v___x_1532_, 4);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1539_ = v___x_1532_;
v_isShared_1540_ = v_isSharedCheck_1565_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_diag_1537_);
lean_inc(v_postponed_1536_);
lean_inc(v_zetaDeltaFVarIds_1535_);
lean_inc(v_cache_1534_);
lean_inc(v_mctx_1533_);
lean_dec(v___x_1532_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1565_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_depth_1541_; lean_object* v_levelAssignDepth_1542_; lean_object* v_lmvarCounter_1543_; lean_object* v_mvarCounter_1544_; lean_object* v_lDecls_1545_; lean_object* v_decls_1546_; lean_object* v_userNames_1547_; lean_object* v_lAssignment_1548_; lean_object* v_eAssignment_1549_; lean_object* v_dAssignment_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1564_; 
v_depth_1541_ = lean_ctor_get(v_mctx_1533_, 0);
v_levelAssignDepth_1542_ = lean_ctor_get(v_mctx_1533_, 1);
v_lmvarCounter_1543_ = lean_ctor_get(v_mctx_1533_, 2);
v_mvarCounter_1544_ = lean_ctor_get(v_mctx_1533_, 3);
v_lDecls_1545_ = lean_ctor_get(v_mctx_1533_, 4);
v_decls_1546_ = lean_ctor_get(v_mctx_1533_, 5);
v_userNames_1547_ = lean_ctor_get(v_mctx_1533_, 6);
v_lAssignment_1548_ = lean_ctor_get(v_mctx_1533_, 7);
v_eAssignment_1549_ = lean_ctor_get(v_mctx_1533_, 8);
v_dAssignment_1550_ = lean_ctor_get(v_mctx_1533_, 9);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_mctx_1533_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1552_ = v_mctx_1533_;
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_dAssignment_1550_);
lean_inc(v_eAssignment_1549_);
lean_inc(v_lAssignment_1548_);
lean_inc(v_userNames_1547_);
lean_inc(v_decls_1546_);
lean_inc(v_lDecls_1545_);
lean_inc(v_mvarCounter_1544_);
lean_inc(v_lmvarCounter_1543_);
lean_inc(v_levelAssignDepth_1542_);
lean_inc(v_depth_1541_);
lean_dec(v_mctx_1533_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1554_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1549_, v_mvarId_1528_, v_val_1529_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 8, v___x_1554_);
v___x_1556_ = v___x_1552_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_depth_1541_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_levelAssignDepth_1542_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_lmvarCounter_1543_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_mvarCounter_1544_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_lDecls_1545_);
lean_ctor_set(v_reuseFailAlloc_1563_, 5, v_decls_1546_);
lean_ctor_set(v_reuseFailAlloc_1563_, 6, v_userNames_1547_);
lean_ctor_set(v_reuseFailAlloc_1563_, 7, v_lAssignment_1548_);
lean_ctor_set(v_reuseFailAlloc_1563_, 8, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1563_, 9, v_dAssignment_1550_);
v___x_1556_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1558_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1556_);
v___x_1558_ = v___x_1539_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_cache_1534_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_zetaDeltaFVarIds_1535_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_postponed_1536_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_diag_1537_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_st_ref_set(v___y_1530_, v___x_1558_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1566_, lean_object* v_val_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1566_, v_val_1567_, v___y_1568_);
lean_dec(v___y_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
lean_inc(v_g_1571_);
v___x_1577_ = l_Lean_MVarId_getType(v_g_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = lean_box(0);
v___x_1580_ = l_Lean_Meta_synthInstance(v_a_1578_, v___x_1579_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1571_, v_a_1581_, v___y_1573_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1582_, 0);
lean_dec(v_unused_1591_);
v___x_1584_ = v___x_1582_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v___x_1582_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_g_1571_);
v_a_1592_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1580_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1580_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_g_1571_);
v_a_1600_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1577_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1577_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1616_){
_start:
{
lean_object* v___f_1617_; lean_object* v___x_1618_; 
v___f_1617_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1618_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1616_, v___f_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1619_, lean_object* v_val_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1619_, v_val_1620_, v___y_1622_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1627_, lean_object* v_val_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1627_, v_val_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1636_, v_x_1637_, v_x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1640_, lean_object* v_x_1641_, size_t v_x_1642_, size_t v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1641_, v_x_1642_, v_x_1643_, v_x_1644_, v_x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
size_t v_x_1169__boxed_1653_; size_t v_x_1170__boxed_1654_; lean_object* v_res_1655_; 
v_x_1169__boxed_1653_ = lean_unbox_usize(v_x_1649_);
lean_dec(v_x_1649_);
v_x_1170__boxed_1654_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_res_1655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1647_, v_x_1648_, v_x_1169__boxed_1653_, v_x_1170__boxed_1654_, v_x_1651_, v_x_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1656_, lean_object* v_n_1657_, lean_object* v_k_1658_, lean_object* v_v_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1657_, v_k_1658_, v_v_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1661_, size_t v_depth_1662_, lean_object* v_keys_1663_, lean_object* v_vals_1664_, lean_object* v_heq_1665_, lean_object* v_i_1666_, lean_object* v_entries_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1662_, v_keys_1663_, v_vals_1664_, v_i_1666_, v_entries_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1669_, lean_object* v_depth_1670_, lean_object* v_keys_1671_, lean_object* v_vals_1672_, lean_object* v_heq_1673_, lean_object* v_i_1674_, lean_object* v_entries_1675_){
_start:
{
size_t v_depth_boxed_1676_; lean_object* v_res_1677_; 
v_depth_boxed_1676_ = lean_unbox_usize(v_depth_1670_);
lean_dec(v_depth_1670_);
v_res_1677_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1669_, v_depth_boxed_1676_, v_keys_1671_, v_vals_1672_, v_heq_1673_, v_i_1674_, v_entries_1675_);
lean_dec_ref(v_vals_1672_);
lean_dec_ref(v_keys_1671_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1679_, v_x_1680_, v_x_1681_, v_x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1684_, lean_object* v_discharge_1685_, lean_object* v_g_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v_g_1686_);
v___x_1692_ = lean_apply_6(v_discharge_1684_, v_g_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, lean_box(0));
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_dec(v_g_1686_);
lean_dec_ref(v_discharge_1685_);
return v___x_1692_;
}
else
{
lean_object* v_a_1693_; uint8_t v___y_1695_; uint8_t v___x_1697_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
v___x_1697_ = l_Lean_Exception_isInterrupt(v_a_1693_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
v___x_1698_ = l_Lean_Exception_isRuntime(v_a_1693_);
v___y_1695_ = v___x_1698_;
goto v___jp_1694_;
}
else
{
lean_dec(v_a_1693_);
v___y_1695_ = v___x_1697_;
goto v___jp_1694_;
}
v___jp_1694_:
{
if (v___y_1695_ == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v___x_1692_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
v___x_1696_ = lean_apply_6(v_discharge_1685_, v_g_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, lean_box(0));
return v___x_1696_;
}
else
{
lean_dec(v_g_1686_);
lean_dec_ref(v_discharge_1685_);
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1699_, lean_object* v_discharge_1700_, lean_object* v_g_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1699_, v_discharge_1700_, v_g_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1708_, lean_object* v_discharge_1709_){
_start:
{
lean_object* v_toApplyRulesConfig_1710_; lean_object* v_toBacktrackConfig_1711_; uint8_t v_backtracking_1712_; uint8_t v_intro_1713_; uint8_t v_constructor_1714_; uint8_t v_suggestions_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1747_; 
v_toApplyRulesConfig_1710_ = lean_ctor_get(v_cfg_1708_, 0);
lean_inc_ref(v_toApplyRulesConfig_1710_);
v_toBacktrackConfig_1711_ = lean_ctor_get(v_toApplyRulesConfig_1710_, 0);
lean_inc_ref(v_toBacktrackConfig_1711_);
v_backtracking_1712_ = lean_ctor_get_uint8(v_cfg_1708_, sizeof(void*)*1);
v_intro_1713_ = lean_ctor_get_uint8(v_cfg_1708_, sizeof(void*)*1 + 1);
v_constructor_1714_ = lean_ctor_get_uint8(v_cfg_1708_, sizeof(void*)*1 + 2);
v_suggestions_1715_ = lean_ctor_get_uint8(v_cfg_1708_, sizeof(void*)*1 + 3);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_cfg_1708_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v_cfg_1708_, 0);
lean_dec(v_unused_1748_);
v___x_1717_ = v_cfg_1708_;
v_isShared_1718_ = v_isSharedCheck_1747_;
goto v_resetjp_1716_;
}
else
{
lean_dec(v_cfg_1708_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1747_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_toApplyConfig_1719_; uint8_t v_transparency_1720_; uint8_t v_symm_1721_; uint8_t v_exfalso_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1745_; 
v_toApplyConfig_1719_ = lean_ctor_get(v_toApplyRulesConfig_1710_, 1);
v_transparency_1720_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1710_, sizeof(void*)*2);
v_symm_1721_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1710_, sizeof(void*)*2 + 1);
v_exfalso_1722_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1710_, sizeof(void*)*2 + 2);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_toApplyRulesConfig_1710_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v_toApplyRulesConfig_1710_, 0);
lean_dec(v_unused_1746_);
v___x_1724_ = v_toApplyRulesConfig_1710_;
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_toApplyConfig_1719_);
lean_dec(v_toApplyRulesConfig_1710_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_maxDepth_1726_; lean_object* v_proc_1727_; lean_object* v_suspend_1728_; lean_object* v_discharge_1729_; uint8_t v_commitIndependentGoals_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1744_; 
v_maxDepth_1726_ = lean_ctor_get(v_toBacktrackConfig_1711_, 0);
v_proc_1727_ = lean_ctor_get(v_toBacktrackConfig_1711_, 1);
v_suspend_1728_ = lean_ctor_get(v_toBacktrackConfig_1711_, 2);
v_discharge_1729_ = lean_ctor_get(v_toBacktrackConfig_1711_, 3);
v_commitIndependentGoals_1730_ = lean_ctor_get_uint8(v_toBacktrackConfig_1711_, sizeof(void*)*4);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_toBacktrackConfig_1711_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1732_ = v_toBacktrackConfig_1711_;
v_isShared_1733_ = v_isSharedCheck_1744_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_discharge_1729_);
lean_inc(v_suspend_1728_);
lean_inc(v_proc_1727_);
lean_inc(v_maxDepth_1726_);
lean_dec(v_toBacktrackConfig_1711_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1744_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___f_1734_; lean_object* v___x_1736_; 
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1734_, 0, v_discharge_1709_);
lean_closure_set(v___f_1734_, 1, v_discharge_1729_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 3, v___f_1734_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_maxDepth_1726_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_proc_1727_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_suspend_1728_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___f_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*4, v_commitIndependentGoals_1730_);
v___x_1736_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1736_);
v___x_1738_ = v___x_1724_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_toApplyConfig_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*2, v_transparency_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*2 + 1, v_symm_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*2 + 2, v_exfalso_1722_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1738_);
v___x_1740_ = v___x_1717_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*1, v_backtracking_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*1 + 1, v_intro_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*1 + 2, v_constructor_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*1 + 3, v_suggestions_1715_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
uint8_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = 1;
v___x_1756_ = l_Lean_Meta_intro1Core(v_g_1749_, v___x_1755_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1775_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1775_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1775_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v_snd_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1773_; 
v_snd_1761_ = lean_ctor_get(v_a_1757_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1757_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v_a_1757_, 0);
lean_dec(v_unused_1774_);
v___x_1763_ = v_a_1757_;
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snd_1761_);
lean_dec(v_a_1757_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_box(0);
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 1);
lean_ctor_set(v___x_1763_, 1, v___x_1765_);
lean_ctor_set(v___x_1763_, 0, v_snd_1761_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_snd_1761_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1768_);
v___x_1770_ = v___x_1759_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1756_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1756_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1792_){
_start:
{
lean_object* v___f_1793_; lean_object* v___x_1794_; 
v___f_1793_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1794_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1792_, v___f_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1806_ = l_Lean_MVarId_constructor(v_g_1799_, v___x_1805_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1807_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
v_a_1816_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1806_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1806_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1832_){
_start:
{
lean_object* v___f_1833_; lean_object* v___x_1834_; 
v___f_1833_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1834_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1832_, v___f_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
lean_inc(v_g_1837_);
v___x_1843_ = l_Lean_MVarId_getType(v_g_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_Meta_synthInstance(v_a_1844_, v___x_1845_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1837_, v_a_1847_, v___y_1839_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1848_, 0);
lean_dec(v_unused_1857_);
v___x_1850_ = v___x_1848_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v___x_1848_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_g_1837_);
v_a_1858_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1846_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1846_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v_g_1837_);
v_a_1866_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1843_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1843_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1882_){
_start:
{
lean_object* v___f_1883_; lean_object* v___x_1884_; 
v___f_1883_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1884_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1882_, v___f_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Lean_Expr_hasMVar(v_e_1885_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_e_1885_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v_mctx_1891_; lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1895_; lean_object* v_cache_1896_; lean_object* v_zetaDeltaFVarIds_1897_; lean_object* v_postponed_1898_; lean_object* v_diag_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1908_; 
v___x_1890_ = lean_st_ref_get(v___y_1886_);
v_mctx_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_mctx_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = l_Lean_instantiateMVarsCore(v_mctx_1891_, v_e_1885_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_fst_1893_);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
lean_inc(v_snd_1894_);
lean_dec_ref(v___x_1892_);
v___x_1895_ = lean_st_ref_take(v___y_1886_);
v_cache_1896_ = lean_ctor_get(v___x_1895_, 1);
v_zetaDeltaFVarIds_1897_ = lean_ctor_get(v___x_1895_, 2);
v_postponed_1898_ = lean_ctor_get(v___x_1895_, 3);
v_diag_1899_ = lean_ctor_get(v___x_1895_, 4);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v___x_1895_, 0);
lean_dec(v_unused_1909_);
v___x_1901_ = v___x_1895_;
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_diag_1899_);
lean_inc(v_postponed_1898_);
lean_inc(v_zetaDeltaFVarIds_1897_);
lean_inc(v_cache_1896_);
lean_dec(v___x_1895_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_snd_1894_);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_snd_1894_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_cache_1896_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_zetaDeltaFVarIds_1897_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_postponed_1898_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_diag_1899_);
v___x_1904_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_st_ref_set(v___y_1886_, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_fst_1893_);
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1910_, v___y_1911_);
lean_dec(v___y_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1914_, v___y_1916_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1928_, lean_object* v_x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1928_, v_x_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1935_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1960_, lean_object* v_mvarId_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1961_, v_x_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1969_, lean_object* v_mvarId_1970_, lean_object* v_x_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1969_, v_mvarId_1970_, v_x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_ref_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1994_; 
v_ref_1984_ = lean_ctor_get(v___y_1981_, 5);
v___x_1985_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1994_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_inc(v_ref_1984_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_ref_1984_);
lean_ctor_set(v___x_1990_, 1, v_a_1986_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_2002_, lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = l_List_reverse___redArg(v_x_2003_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
else
{
lean_object* v_head_2011_; lean_object* v_tail_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2032_; 
v_head_2011_ = lean_ctor_get(v_x_2002_, 0);
v_tail_2012_ = lean_ctor_get(v_x_2002_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_2002_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2014_ = v_x_2002_;
v_isShared_2015_ = v_isSharedCheck_2032_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_tail_2012_);
lean_inc(v_head_2011_);
lean_dec(v_x_2002_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2032_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_inc(v_head_2011_);
v___x_2016_ = l_Lean_Expr_mvar___override(v_head_2011_);
v___x_2017_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_2017_, 0, v___x_2016_);
v___x_2018_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_2011_, v___x_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v_x_2003_);
lean_ctor_set(v___x_2014_, 0, v_a_2019_);
v___x_2021_ = v___x_2014_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2019_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_x_2003_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
v_x_2002_ = v_tail_2012_;
v_x_2003_ = v___x_2021_;
goto _start;
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_del_object(v___x_2014_);
lean_dec(v_tail_2012_);
lean_dec(v_x_2003_);
v_a_2024_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2018_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2018_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2033_, v_x_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2040_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2043_ = l_Lean_stringToMessageData(v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2044_, lean_object* v_proc_2045_, lean_object* v_orig_2046_, lean_object* v_goals_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_box(0);
lean_inc(v_orig_2046_);
v___x_2054_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2046_, v___x_2053_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
v___x_2056_ = lean_apply_6(v_test_2044_, v_a_2055_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, lean_box(0));
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; uint8_t v___x_2058_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = lean_unbox(v_a_2057_);
lean_dec(v_a_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_goals_2047_);
lean_dec(v_orig_2046_);
lean_dec_ref(v_proc_2045_);
v___x_2059_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2060_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2059_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v___x_2069_; 
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
v___x_2069_ = lean_apply_7(v_proc_2045_, v_orig_2046_, v_goals_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, lean_box(0));
return v___x_2069_;
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_goals_2047_);
lean_dec(v_orig_2046_);
lean_dec_ref(v_proc_2045_);
v_a_2070_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2056_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2056_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_goals_2047_);
lean_dec(v_orig_2046_);
lean_dec_ref(v_proc_2045_);
lean_dec_ref(v_test_2044_);
v_a_2078_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2054_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2054_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2086_, lean_object* v_proc_2087_, lean_object* v_orig_2088_, lean_object* v_goals_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2086_, v_proc_2087_, v_orig_2088_, v_goals_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2096_, lean_object* v_test_2097_){
_start:
{
lean_object* v_toApplyRulesConfig_2098_; lean_object* v_toBacktrackConfig_2099_; uint8_t v_backtracking_2100_; uint8_t v_intro_2101_; uint8_t v_constructor_2102_; uint8_t v_suggestions_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2135_; 
v_toApplyRulesConfig_2098_ = lean_ctor_get(v_cfg_2096_, 0);
lean_inc_ref(v_toApplyRulesConfig_2098_);
v_toBacktrackConfig_2099_ = lean_ctor_get(v_toApplyRulesConfig_2098_, 0);
lean_inc_ref(v_toBacktrackConfig_2099_);
v_backtracking_2100_ = lean_ctor_get_uint8(v_cfg_2096_, sizeof(void*)*1);
v_intro_2101_ = lean_ctor_get_uint8(v_cfg_2096_, sizeof(void*)*1 + 1);
v_constructor_2102_ = lean_ctor_get_uint8(v_cfg_2096_, sizeof(void*)*1 + 2);
v_suggestions_2103_ = lean_ctor_get_uint8(v_cfg_2096_, sizeof(void*)*1 + 3);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_cfg_2096_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v_cfg_2096_, 0);
lean_dec(v_unused_2136_);
v___x_2105_ = v_cfg_2096_;
v_isShared_2106_ = v_isSharedCheck_2135_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v_cfg_2096_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2135_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_toApplyConfig_2107_; uint8_t v_transparency_2108_; uint8_t v_symm_2109_; uint8_t v_exfalso_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2133_; 
v_toApplyConfig_2107_ = lean_ctor_get(v_toApplyRulesConfig_2098_, 1);
v_transparency_2108_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2098_, sizeof(void*)*2);
v_symm_2109_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2098_, sizeof(void*)*2 + 1);
v_exfalso_2110_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2098_, sizeof(void*)*2 + 2);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_toApplyRulesConfig_2098_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_toApplyRulesConfig_2098_, 0);
lean_dec(v_unused_2134_);
v___x_2112_ = v_toApplyRulesConfig_2098_;
v_isShared_2113_ = v_isSharedCheck_2133_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_toApplyConfig_2107_);
lean_dec(v_toApplyRulesConfig_2098_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2133_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_maxDepth_2114_; lean_object* v_proc_2115_; lean_object* v_suspend_2116_; lean_object* v_discharge_2117_; uint8_t v_commitIndependentGoals_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2132_; 
v_maxDepth_2114_ = lean_ctor_get(v_toBacktrackConfig_2099_, 0);
v_proc_2115_ = lean_ctor_get(v_toBacktrackConfig_2099_, 1);
v_suspend_2116_ = lean_ctor_get(v_toBacktrackConfig_2099_, 2);
v_discharge_2117_ = lean_ctor_get(v_toBacktrackConfig_2099_, 3);
v_commitIndependentGoals_2118_ = lean_ctor_get_uint8(v_toBacktrackConfig_2099_, sizeof(void*)*4);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_toBacktrackConfig_2099_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2120_ = v_toBacktrackConfig_2099_;
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_discharge_2117_);
lean_inc(v_suspend_2116_);
lean_inc(v_proc_2115_);
lean_inc(v_maxDepth_2114_);
lean_dec(v_toBacktrackConfig_2099_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___f_2122_; lean_object* v___x_2124_; 
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2122_, 0, v_test_2097_);
lean_closure_set(v___f_2122_, 1, v_proc_2115_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___f_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_maxDepth_2114_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___f_2122_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_suspend_2116_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_discharge_2117_);
lean_ctor_set_uint8(v_reuseFailAlloc_2131_, sizeof(void*)*4, v_commitIndependentGoals_2118_);
v___x_2124_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2124_);
v___x_2126_ = v___x_2112_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_toApplyConfig_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*2, v_transparency_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*2 + 1, v_symm_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*2 + 2, v_exfalso_2110_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2126_);
v___x_2128_ = v___x_2105_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*1, v_backtracking_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*1 + 1, v_intro_2101_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*1 + 2, v_constructor_2102_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*1 + 3, v_suggestions_2103_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2137_, lean_object* v_msg_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2145_, v_msg_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2152_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
uint8_t v___x_2154_; 
v___x_2154_ = 0;
return v___x_2154_;
}
else
{
lean_object* v_head_2155_; lean_object* v_tail_2156_; uint8_t v___x_2157_; 
v_head_2155_ = lean_ctor_get(v_x_2153_, 0);
v_tail_2156_ = lean_ctor_get(v_x_2153_, 1);
v___x_2157_ = l_Lean_Expr_hasMVar(v_head_2155_);
if (v___x_2157_ == 0)
{
v_x_2153_ = v_tail_2156_;
goto _start;
}
else
{
return v___x_2157_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0___boxed(lean_object* v_x_2159_){
_start:
{
uint8_t v_res_2160_; lean_object* v_r_2161_; 
v_res_2160_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_x_2159_);
lean_dec(v_x_2159_);
v_r_2161_ = lean_box(v_res_2160_);
return v_r_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2162_, lean_object* v_sols_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v___x_2169_; 
v___x_2169_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions_spec__0(v_sols_2163_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
lean_inc(v___y_2167_);
lean_inc_ref(v___y_2166_);
lean_inc(v___y_2165_);
lean_inc_ref(v___y_2164_);
v___x_2170_ = lean_apply_6(v_test_2162_, v_sols_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, lean_box(0));
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_sols_2163_);
lean_dec_ref(v_test_2162_);
v___x_2171_ = lean_box(v___x_2169_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2173_, lean_object* v_sols_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2173_, v_sols_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2181_, lean_object* v_test_2182_){
_start:
{
lean_object* v___f_2183_; lean_object* v___x_2184_; 
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2183_, 0, v_test_2182_);
v___x_2184_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2181_, v___f_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(lean_object* v_e_2185_, lean_object* v_x_2186_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 0)
{
uint8_t v___x_2187_; 
lean_dec_ref(v_e_2185_);
v___x_2187_ = 0;
return v___x_2187_;
}
else
{
lean_object* v_head_2188_; lean_object* v_tail_2189_; uint8_t v___x_2190_; 
v_head_2188_ = lean_ctor_get(v_x_2186_, 0);
v_tail_2189_ = lean_ctor_get(v_x_2186_, 1);
lean_inc_ref(v_e_2185_);
v___x_2190_ = l_Lean_Expr_occurs(v_e_2185_, v_head_2188_);
if (v___x_2190_ == 0)
{
v_x_2186_ = v_tail_2189_;
goto _start;
}
else
{
lean_dec_ref(v_e_2185_);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0___boxed(lean_object* v_e_2192_, lean_object* v_x_2193_){
_start:
{
uint8_t v_res_2194_; lean_object* v_r_2195_; 
v_res_2194_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_e_2192_, v_x_2193_);
lean_dec(v_x_2193_);
v_r_2195_ = lean_box(v_res_2194_);
return v_r_2195_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(lean_object* v_sols_2196_, lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 0)
{
uint8_t v___x_2198_; 
v___x_2198_ = 1;
return v___x_2198_;
}
else
{
lean_object* v_head_2199_; lean_object* v_tail_2200_; uint8_t v___x_2201_; 
v_head_2199_ = lean_ctor_get(v_x_2197_, 0);
lean_inc(v_head_2199_);
v_tail_2200_ = lean_ctor_get(v_x_2197_, 1);
lean_inc(v_tail_2200_);
lean_dec_ref(v_x_2197_);
v___x_2201_ = l_List_any___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__0(v_head_2199_, v_sols_2196_);
if (v___x_2201_ == 0)
{
lean_dec(v_tail_2200_);
return v___x_2201_;
}
else
{
v_x_2197_ = v_tail_2200_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1___boxed(lean_object* v_sols_2203_, lean_object* v_x_2204_){
_start:
{
uint8_t v_res_2205_; lean_object* v_r_2206_; 
v_res_2205_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2203_, v_x_2204_);
lean_dec(v_sols_2203_);
v_r_2206_ = lean_box(v_res_2205_);
return v_r_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_use_2207_, lean_object* v_sols_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = l_List_all___at___00Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll_spec__1(v_sols_2208_, v_use_2207_);
v___x_2215_ = lean_box(v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_use_2217_, lean_object* v_sols_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_use_2217_, v_sols_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v_sols_2218_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2225_, lean_object* v_use_2226_){
_start:
{
lean_object* v___f_2227_; lean_object* v___x_2228_; 
v___f_2227_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2227_, 0, v_use_2226_);
v___x_2228_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2225_, v___f_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2229_){
_start:
{
lean_object* v___y_2231_; lean_object* v_toApplyRulesConfig_2232_; uint8_t v_backtracking_2233_; uint8_t v_intro_2234_; uint8_t v_constructor_2235_; uint8_t v_suggestions_2236_; uint8_t v_intro_2240_; 
v_intro_2240_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1 + 1);
if (v_intro_2240_ == 0)
{
lean_object* v_toApplyRulesConfig_2241_; uint8_t v_backtracking_2242_; uint8_t v_constructor_2243_; uint8_t v_suggestions_2244_; 
v_toApplyRulesConfig_2241_ = lean_ctor_get(v_cfg_2229_, 0);
lean_inc_ref(v_toApplyRulesConfig_2241_);
v_backtracking_2242_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1);
v_constructor_2243_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1 + 2);
v_suggestions_2244_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1 + 3);
v___y_2231_ = v_cfg_2229_;
v_toApplyRulesConfig_2232_ = v_toApplyRulesConfig_2241_;
v_backtracking_2233_ = v_backtracking_2242_;
v_intro_2234_ = v_intro_2240_;
v_constructor_2235_ = v_constructor_2243_;
v_suggestions_2236_ = v_suggestions_2244_;
goto v___jp_2230_;
}
else
{
lean_object* v_toApplyRulesConfig_2245_; uint8_t v_backtracking_2246_; uint8_t v_constructor_2247_; uint8_t v_suggestions_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2262_; 
v_toApplyRulesConfig_2245_ = lean_ctor_get(v_cfg_2229_, 0);
v_backtracking_2246_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1);
v_constructor_2247_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1 + 2);
v_suggestions_2248_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*1 + 3);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_cfg_2229_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2250_ = v_cfg_2229_;
v_isShared_2251_ = v_isSharedCheck_2262_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_toApplyRulesConfig_2245_);
lean_dec(v_cfg_2229_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2262_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
uint8_t v___x_2252_; lean_object* v___x_2254_; 
v___x_2252_ = 0;
if (v_isShared_2251_ == 0)
{
v___x_2254_ = v___x_2250_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_toApplyRulesConfig_2245_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, sizeof(void*)*1, v_backtracking_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, sizeof(void*)*1 + 2, v_constructor_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2261_, sizeof(void*)*1 + 3, v_suggestions_2248_);
v___x_2254_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2255_; lean_object* v_toApplyRulesConfig_2256_; uint8_t v_backtracking_2257_; uint8_t v_intro_2258_; uint8_t v_constructor_2259_; uint8_t v_suggestions_2260_; 
lean_ctor_set_uint8(v___x_2254_, sizeof(void*)*1 + 1, v___x_2252_);
v___x_2255_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2254_);
v_toApplyRulesConfig_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref(v_toApplyRulesConfig_2256_);
v_backtracking_2257_ = lean_ctor_get_uint8(v___x_2255_, sizeof(void*)*1);
v_intro_2258_ = lean_ctor_get_uint8(v___x_2255_, sizeof(void*)*1 + 1);
v_constructor_2259_ = lean_ctor_get_uint8(v___x_2255_, sizeof(void*)*1 + 2);
v_suggestions_2260_ = lean_ctor_get_uint8(v___x_2255_, sizeof(void*)*1 + 3);
v___y_2231_ = v___x_2255_;
v_toApplyRulesConfig_2232_ = v_toApplyRulesConfig_2256_;
v_backtracking_2233_ = v_backtracking_2257_;
v_intro_2234_ = v_intro_2258_;
v_constructor_2235_ = v_constructor_2259_;
v_suggestions_2236_ = v_suggestions_2260_;
goto v___jp_2230_;
}
}
}
v___jp_2230_:
{
if (v_constructor_2235_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2232_);
return v___y_2231_;
}
else
{
uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v___y_2231_);
v___x_2237_ = 0;
v___x_2238_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2238_, 0, v_toApplyRulesConfig_2232_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1, v_backtracking_2233_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1 + 1, v_intro_2234_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1 + 2, v___x_2237_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*1 + 3, v_suggestions_2236_);
v___x_2239_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2238_);
return v___x_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2263_, lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = l_List_reverse___redArg(v_x_2264_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
else
{
lean_object* v_head_2274_; lean_object* v_tail_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2293_; 
v_head_2274_ = lean_ctor_get(v_x_2263_, 0);
v_tail_2275_ = lean_ctor_get(v_x_2263_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2277_ = v_x_2263_;
v_isShared_2278_ = v_isSharedCheck_2293_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_tail_2275_);
lean_inc(v_head_2274_);
lean_dec(v_x_2263_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2293_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; 
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
v___x_2279_ = lean_apply_7(v_head_2274_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, lean_box(0));
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v_x_2264_);
lean_ctor_set(v___x_2277_, 0, v_a_2280_);
v___x_2282_ = v___x_2277_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2280_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_x_2264_);
v___x_2282_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
v_x_2263_ = v_tail_2275_;
v_x_2264_ = v___x_2282_;
goto _start;
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2277_);
lean_dec(v_tail_2275_);
lean_dec(v_x_2264_);
v_a_2285_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2279_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2279_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2294_, v_x_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2304_, lean_object* v_cfg_2305_, lean_object* v_lemmas_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; 
lean_inc(v___y_2312_);
lean_inc_ref(v___y_2311_);
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
v___x_2314_ = lean_apply_8(v_ctx_2304_, v_cfg_2305_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, lean_box(0));
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref(v___x_2314_);
v___x_2316_ = lean_box(0);
v___x_2317_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2306_, v___x_2316_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = l_List_appendTR___redArg(v_a_2315_, v_a_2318_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2322_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
else
{
lean_dec(v_a_2315_);
return v___x_2317_;
}
}
else
{
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_lemmas_2306_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2327_, lean_object* v_cfg_2328_, lean_object* v_lemmas_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2327_, v_cfg_2328_, v_lemmas_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2338_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = 0;
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2340_){
_start:
{
uint8_t v_res_2341_; lean_object* v_r_2342_; 
v_res_2341_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2340_);
lean_dec(v_x_2340_);
v_r_2342_ = lean_box(v_res_2341_);
return v_r_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2343_, lean_object* v___x_2344_, lean_object* v___x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2343_, v___x_2344_, v___x_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2360_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_fst_2356_; lean_object* v___x_2358_; 
v_fst_2356_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_fst_2356_);
lean_dec(v_a_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v_fst_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_fst_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2351_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2351_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2369_, lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2369_, v___x_2370_, v___x_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2392_, lean_object* v_g_2393_, lean_object* v_lemmas_2394_, lean_object* v_ctx_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___f_2404_; lean_object* v___x_2405_; 
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2401_, 0, v_ctx_2395_);
lean_closure_set(v___f_2401_, 1, v_cfg_2392_);
lean_closure_set(v___f_2401_, 2, v_lemmas_2394_);
v___x_2402_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2403_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2404_, 0, v___f_2401_);
lean_closure_set(v___f_2404_, 1, v___x_2402_);
lean_closure_set(v___f_2404_, 2, v___x_2403_);
v___x_2405_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2393_, v___f_2404_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2406_, lean_object* v_g_2407_, lean_object* v_lemmas_2408_, lean_object* v_ctx_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2406_, v_g_2407_, v_lemmas_2408_, v_ctx_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2416_, lean_object* v_lemmas_2417_, lean_object* v_ctx_2418_, lean_object* v_g_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
lean_inc(v_g_2419_);
lean_inc_ref(v_cfg_2416_);
v___x_2425_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2416_, v_g_2419_, v_lemmas_2417_, v_ctx_2418_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_toApplyRulesConfig_2426_; lean_object* v_a_2427_; lean_object* v_toApplyConfig_2428_; uint8_t v_transparency_2429_; lean_object* v___x_2430_; 
v_toApplyRulesConfig_2426_ = lean_ctor_get(v_cfg_2416_, 0);
lean_inc_ref(v_toApplyRulesConfig_2426_);
lean_dec_ref(v_cfg_2416_);
v_a_2427_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2427_);
lean_dec_ref(v___x_2425_);
v_toApplyConfig_2428_ = lean_ctor_get(v_toApplyRulesConfig_2426_, 1);
lean_inc_ref(v_toApplyConfig_2428_);
v_transparency_2429_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2426_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2426_);
v___x_2430_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2428_, v_transparency_2429_, v_a_2427_, v_g_2419_, v_a_2421_, v_a_2423_);
return v___x_2430_;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_g_2419_);
lean_dec_ref(v_cfg_2416_);
v_a_2431_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2425_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2425_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2439_, lean_object* v_lemmas_2440_, lean_object* v_ctx_2441_, lean_object* v_g_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2439_, v_lemmas_2440_, v_ctx_2441_, v_g_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2449_, lean_object* v_lemmas_2450_, lean_object* v_ctx_2451_, lean_object* v_g_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; 
lean_inc(v_g_2452_);
lean_inc_ref(v_cfg_2449_);
v___x_2458_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2449_, v_g_2452_, v_lemmas_2450_, v_ctx_2451_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_toApplyRulesConfig_2459_; lean_object* v_a_2460_; lean_object* v_toApplyConfig_2461_; uint8_t v_transparency_2462_; lean_object* v___x_2463_; 
v_toApplyRulesConfig_2459_ = lean_ctor_get(v_cfg_2449_, 0);
lean_inc_ref(v_toApplyRulesConfig_2459_);
lean_dec_ref(v_cfg_2449_);
v_a_2460_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2460_);
lean_dec_ref(v___x_2458_);
v_toApplyConfig_2461_ = lean_ctor_get(v_toApplyRulesConfig_2459_, 1);
lean_inc_ref(v_toApplyConfig_2461_);
v_transparency_2462_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2459_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2459_);
v___x_2463_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2461_, v_transparency_2462_, v_a_2460_, v_g_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
return v___x_2463_;
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_g_2452_);
lean_dec_ref(v_cfg_2449_);
v_a_2464_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2458_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2458_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2472_, lean_object* v_lemmas_2473_, lean_object* v_ctx_2474_, lean_object* v_g_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2472_, v_lemmas_2473_, v_ctx_2474_, v_g_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
return v_res_2481_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2482_, lean_object* v_i_2483_, lean_object* v_k_2484_){
_start:
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = lean_array_get_size(v_keys_2482_);
v___x_2486_ = lean_nat_dec_lt(v_i_2483_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_dec(v_i_2483_);
return v___x_2486_;
}
else
{
lean_object* v_k_x27_2487_; uint8_t v___x_2488_; 
v_k_x27_2487_ = lean_array_fget_borrowed(v_keys_2482_, v_i_2483_);
v___x_2488_ = l_Lean_instBEqMVarId_beq(v_k_2484_, v_k_x27_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_unsigned_to_nat(1u);
v___x_2490_ = lean_nat_add(v_i_2483_, v___x_2489_);
lean_dec(v_i_2483_);
v_i_2483_ = v___x_2490_;
goto _start;
}
else
{
lean_dec(v_i_2483_);
return v___x_2488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2492_, lean_object* v_i_2493_, lean_object* v_k_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2492_, v_i_2493_, v_k_2494_);
lean_dec(v_k_2494_);
lean_dec_ref(v_keys_2492_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2497_, size_t v_x_2498_, lean_object* v_x_2499_){
_start:
{
if (lean_obj_tag(v_x_2497_) == 0)
{
lean_object* v_es_2500_; lean_object* v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; lean_object* v_j_2505_; lean_object* v___x_2506_; 
v_es_2500_ = lean_ctor_get(v_x_2497_, 0);
v___x_2501_ = lean_box(2);
v___x_2502_ = ((size_t)5ULL);
v___x_2503_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2504_ = lean_usize_land(v_x_2498_, v___x_2503_);
v_j_2505_ = lean_usize_to_nat(v___x_2504_);
v___x_2506_ = lean_array_get_borrowed(v___x_2501_, v_es_2500_, v_j_2505_);
lean_dec(v_j_2505_);
switch(lean_obj_tag(v___x_2506_))
{
case 0:
{
lean_object* v_key_2507_; uint8_t v___x_2508_; 
v_key_2507_ = lean_ctor_get(v___x_2506_, 0);
v___x_2508_ = l_Lean_instBEqMVarId_beq(v_x_2499_, v_key_2507_);
return v___x_2508_;
}
case 1:
{
lean_object* v_node_2509_; size_t v___x_2510_; 
v_node_2509_ = lean_ctor_get(v___x_2506_, 0);
v___x_2510_ = lean_usize_shift_right(v_x_2498_, v___x_2502_);
v_x_2497_ = v_node_2509_;
v_x_2498_ = v___x_2510_;
goto _start;
}
default: 
{
uint8_t v___x_2512_; 
v___x_2512_ = 0;
return v___x_2512_;
}
}
}
else
{
lean_object* v_ks_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_ks_2513_ = lean_ctor_get(v_x_2497_, 0);
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2513_, v___x_2514_, v_x_2499_);
return v___x_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2516_, lean_object* v_x_2517_, lean_object* v_x_2518_){
_start:
{
size_t v_x_2218__boxed_2519_; uint8_t v_res_2520_; lean_object* v_r_2521_; 
v_x_2218__boxed_2519_ = lean_unbox_usize(v_x_2517_);
lean_dec(v_x_2517_);
v_res_2520_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2516_, v_x_2218__boxed_2519_, v_x_2518_);
lean_dec(v_x_2518_);
lean_dec_ref(v_x_2516_);
v_r_2521_ = lean_box(v_res_2520_);
return v_r_2521_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
uint64_t v___x_2524_; size_t v___x_2525_; uint8_t v___x_2526_; 
v___x_2524_ = l_Lean_instHashableMVarId_hash(v_x_2523_);
v___x_2525_ = lean_uint64_to_usize(v___x_2524_);
v___x_2526_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2522_, v___x_2525_, v_x_2523_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2527_, lean_object* v_x_2528_){
_start:
{
uint8_t v_res_2529_; lean_object* v_r_2530_; 
v_res_2529_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2527_, v_x_2528_);
lean_dec(v_x_2528_);
lean_dec_ref(v_x_2527_);
v_r_2530_ = lean_box(v_res_2529_);
return v_r_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v_mctx_2535_; lean_object* v_eAssignment_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2534_ = lean_st_ref_get(v___y_2532_);
v_mctx_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_mctx_2535_);
lean_dec(v___x_2534_);
v_eAssignment_2536_ = lean_ctor_get(v_mctx_2535_, 8);
lean_inc_ref(v_eAssignment_2536_);
lean_dec_ref(v_mctx_2535_);
v___x_2537_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2536_, v_mvarId_2531_);
lean_dec_ref(v_eAssignment_2536_);
v___x_2538_ = lean_box(v___x_2537_);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec(v_mvarId_2540_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2544_, lean_object* v_x_2545_){
_start:
{
if (lean_obj_tag(v_x_2545_) == 0)
{
return v_x_2544_;
}
else
{
lean_object* v_head_2546_; lean_object* v_tail_2547_; lean_object* v___x_2548_; 
v_head_2546_ = lean_ctor_get(v_x_2545_, 0);
lean_inc(v_head_2546_);
v_tail_2547_ = lean_ctor_get(v_x_2545_, 1);
lean_inc(v_tail_2547_);
lean_dec_ref(v_x_2545_);
v___x_2548_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2544_, v_head_2546_);
v_x_2544_ = v___x_2548_;
v_x_2545_ = v_tail_2547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2550_, lean_object* v_a_2551_, uint8_t v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
if (lean_obj_tag(v_a_2553_) == 0)
{
if (lean_obj_tag(v_a_2554_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec(v_a_2551_);
lean_dec_ref(v_f_2550_);
v___x_2561_ = lean_box(v_a_2552_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v_a_2555_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
else
{
lean_object* v_head_2564_; lean_object* v_tail_2565_; 
v_head_2564_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_head_2564_);
v_tail_2565_ = lean_ctor_get(v_a_2554_, 1);
lean_inc(v_tail_2565_);
lean_dec_ref(v_a_2554_);
v_a_2553_ = v_head_2564_;
v_a_2554_ = v_tail_2565_;
goto _start;
}
}
else
{
lean_object* v_head_2567_; lean_object* v_tail_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2611_; 
v_head_2567_ = lean_ctor_get(v_a_2553_, 0);
v_tail_2568_ = lean_ctor_get(v_a_2553_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2553_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2570_ = v_a_2553_;
v_isShared_2571_ = v_isSharedCheck_2611_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_tail_2568_);
lean_inc(v_head_2567_);
lean_dec(v_a_2553_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2611_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2610_; 
v___x_2572_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2567_, v___y_2557_);
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2610_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2610_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_unbox(v_a_2573_);
lean_dec(v_a_2573_);
if (v___x_2577_ == 0)
{
lean_object* v_zero_2578_; uint8_t v_isZero_2579_; 
v_zero_2578_ = lean_unsigned_to_nat(0u);
v_isZero_2579_ = lean_nat_dec_eq(v_a_2551_, v_zero_2578_);
if (v_isZero_2579_ == 1)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_del_object(v___x_2570_);
lean_dec(v_a_2551_);
lean_dec_ref(v_f_2550_);
v___x_2580_ = lean_array_push(v_a_2555_, v_head_2567_);
v___x_2581_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2580_, v_tail_2568_);
v___x_2582_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2581_, v_a_2554_);
v___x_2583_ = lean_box(v_a_2552_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2584_);
v___x_2586_ = v___x_2575_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_del_object(v___x_2575_);
lean_inc_ref(v_f_2550_);
lean_inc(v_head_2567_);
v___x_2588_ = lean_apply_1(v_f_2550_, v_head_2567_);
v___x_2589_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2588_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v_one_2591_; lean_object* v_n_2592_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
v_one_2591_ = lean_unsigned_to_nat(1u);
v_n_2592_ = lean_nat_sub(v_a_2551_, v_one_2591_);
lean_dec(v_a_2551_);
if (lean_obj_tag(v_a_2590_) == 0)
{
lean_object* v___x_2593_; 
lean_del_object(v___x_2570_);
v___x_2593_ = lean_array_push(v_a_2555_, v_head_2567_);
v_a_2551_ = v_n_2592_;
v_a_2553_ = v_tail_2568_;
v_a_2555_ = v___x_2593_;
goto _start;
}
else
{
lean_object* v_val_2595_; uint8_t v___x_2596_; lean_object* v___x_2598_; 
lean_dec(v_head_2567_);
v_val_2595_ = lean_ctor_get(v_a_2590_, 0);
lean_inc(v_val_2595_);
lean_dec_ref(v_a_2590_);
v___x_2596_ = 1;
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v_a_2554_);
lean_ctor_set(v___x_2570_, 0, v_tail_2568_);
v___x_2598_ = v___x_2570_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_tail_2568_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_a_2554_);
v___x_2598_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
v_a_2551_ = v_n_2592_;
v_a_2552_ = v___x_2596_;
v_a_2553_ = v_val_2595_;
v_a_2554_ = v___x_2598_;
goto _start;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_del_object(v___x_2570_);
lean_dec(v_tail_2568_);
lean_dec(v_head_2567_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec(v_a_2551_);
lean_dec_ref(v_f_2550_);
v_a_2601_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2589_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2589_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
else
{
lean_del_object(v___x_2575_);
lean_del_object(v___x_2570_);
lean_dec(v_head_2567_);
v_a_2553_ = v_tail_2568_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
uint8_t v_a_2299__boxed_2623_; lean_object* v_res_2624_; 
v_a_2299__boxed_2623_ = lean_unbox(v_a_2614_);
v_res_2624_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2612_, v_a_2613_, v_a_2299__boxed_2623_, v_a_2615_, v_a_2616_, v_a_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2625_, size_t v_i_2626_, size_t v_stop_2627_, lean_object* v_b_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_a_2635_; uint8_t v___x_2639_; 
v___x_2639_ = lean_usize_dec_eq(v_i_2626_, v_stop_2627_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2643_; 
v___x_2640_ = lean_array_uget_borrowed(v_as_2625_, v_i_2626_);
v___x_2643_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2640_, v___y_2630_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; uint8_t v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
v___x_2645_ = lean_unbox(v_a_2644_);
lean_dec(v_a_2644_);
if (v___x_2645_ == 0)
{
goto v___jp_2641_;
}
else
{
v_a_2635_ = v_b_2628_;
goto v___jp_2634_;
}
}
else
{
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2646_; uint8_t v___x_2647_; 
v_a_2646_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2643_);
v___x_2647_ = lean_unbox(v_a_2646_);
lean_dec(v_a_2646_);
if (v___x_2647_ == 0)
{
v_a_2635_ = v_b_2628_;
goto v___jp_2634_;
}
else
{
goto v___jp_2641_;
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref(v_b_2628_);
v_a_2648_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2643_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2643_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
v___jp_2641_:
{
lean_object* v___x_2642_; 
lean_inc(v___x_2640_);
v___x_2642_ = lean_array_push(v_b_2628_, v___x_2640_);
v_a_2635_ = v___x_2642_;
goto v___jp_2634_;
}
}
else
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_b_2628_);
return v___x_2656_;
}
v___jp_2634_:
{
size_t v___x_2636_; size_t v___x_2637_; 
v___x_2636_ = ((size_t)1ULL);
v___x_2637_ = lean_usize_add(v_i_2626_, v___x_2636_);
v_i_2626_ = v___x_2637_;
v_b_2628_ = v_a_2635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2657_, lean_object* v_i_2658_, lean_object* v_stop_2659_, lean_object* v_b_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
size_t v_i_boxed_2666_; size_t v_stop_boxed_2667_; lean_object* v_res_2668_; 
v_i_boxed_2666_ = lean_unbox_usize(v_i_2658_);
lean_dec(v_i_2658_);
v_stop_boxed_2667_ = lean_unbox_usize(v_stop_2659_);
lean_dec(v_stop_2659_);
v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2657_, v_i_boxed_2666_, v_stop_boxed_2667_, v_b_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec_ref(v_as_2657_);
return v_res_2668_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2672_ = lean_array_to_list(v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2673_, lean_object* v_goals_2674_, lean_object* v_maxIters_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2681_ = 0;
v___x_2682_ = lean_box(0);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2685_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2673_, v_maxIters_2675_, v___x_2681_, v_goals_2674_, v___x_2682_, v___x_2684_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2735_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2735_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2735_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2734_; 
v_fst_2690_ = lean_ctor_get(v_a_2686_, 0);
v_snd_2691_ = lean_ctor_get(v_a_2686_, 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_a_2686_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2693_ = v_a_2686_;
v_isShared_2694_ = v_isSharedCheck_2734_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snd_2691_);
lean_inc(v_fst_2690_);
lean_dec(v_a_2686_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2734_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_____do__lift_2696_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = lean_array_get_size(v_snd_2691_);
v___x_2705_ = lean_nat_dec_lt(v___x_2683_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_del_object(v___x_2693_);
lean_dec(v_snd_2691_);
lean_del_object(v___x_2688_);
v___x_2706_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_fst_2690_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_le(v___x_2704_, v___x_2704_);
if (v___x_2709_ == 0)
{
if (v___x_2705_ == 0)
{
lean_dec(v_snd_2691_);
v_____do__lift_2696_ = v___x_2684_;
goto v___jp_2695_;
}
else
{
size_t v___x_2710_; size_t v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = ((size_t)0ULL);
v___x_2711_ = lean_usize_of_nat(v___x_2704_);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2691_, v___x_2710_, v___x_2711_, v___x_2684_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v_snd_2691_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref(v___x_2712_);
v_____do__lift_2696_ = v_a_2713_;
goto v___jp_2695_;
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_del_object(v___x_2693_);
lean_dec(v_fst_2690_);
lean_del_object(v___x_2688_);
v_a_2714_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2712_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2712_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
else
{
size_t v___x_2722_; size_t v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = ((size_t)0ULL);
v___x_2723_ = lean_usize_of_nat(v___x_2704_);
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2691_, v___x_2722_, v___x_2723_, v___x_2684_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v_snd_2691_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref(v___x_2724_);
v_____do__lift_2696_ = v_a_2725_;
goto v___jp_2695_;
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_del_object(v___x_2693_);
lean_dec(v_fst_2690_);
lean_del_object(v___x_2688_);
v_a_2726_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2724_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2724_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_array_to_list(v_____do__lift_2696_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2697_);
v___x_2699_ = v___x_2693_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_fst_2690_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2699_);
v___x_2701_ = v___x_2688_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
v_a_2736_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2685_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2685_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2744_, lean_object* v_goals_2745_, lean_object* v_maxIters_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2744_, v_goals_2745_, v_maxIters_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2752_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2756_, lean_object* v_goals_2757_, lean_object* v_maxIters_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2756_, v_goals_2757_, v_maxIters_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2777_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2777_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2777_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v_fst_2769_; uint8_t v___x_2770_; 
v_fst_2769_ = lean_ctor_get(v_a_2765_, 0);
v___x_2770_ = lean_unbox(v_fst_2769_);
if (v___x_2770_ == 1)
{
lean_object* v_snd_2771_; lean_object* v___x_2773_; 
v_snd_2771_ = lean_ctor_get(v_a_2765_, 1);
lean_inc(v_snd_2771_);
lean_dec(v_a_2765_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_snd_2771_);
v___x_2773_ = v___x_2767_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_snd_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_del_object(v___x_2767_);
lean_dec(v_a_2765_);
v___x_2775_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2776_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2775_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2764_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2764_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2786_, lean_object* v_goals_2787_, lean_object* v_maxIters_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2786_, v_goals_2787_, v_maxIters_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2795_, lean_object* v_ctx_2796_, lean_object* v_cfg_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
uint8_t v_backtracking_2804_; 
v_backtracking_2804_ = lean_ctor_get_uint8(v_cfg_2797_, sizeof(void*)*1);
if (v_backtracking_2804_ == 0)
{
lean_object* v_toApplyRulesConfig_2805_; lean_object* v_toBacktrackConfig_2806_; lean_object* v_maxDepth_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_toApplyRulesConfig_2805_ = lean_ctor_get(v_cfg_2797_, 0);
v_toBacktrackConfig_2806_ = lean_ctor_get(v_toApplyRulesConfig_2805_, 0);
v_maxDepth_2807_ = lean_ctor_get(v_toBacktrackConfig_2806_, 0);
lean_inc(v_maxDepth_2807_);
v___x_2808_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2808_, 0, v_cfg_2797_);
lean_closure_set(v___x_2808_, 1, v_lemmas_2795_);
lean_closure_set(v___x_2808_, 2, v_ctx_2796_);
v___x_2809_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2808_, v_a_2798_, v_maxDepth_2807_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2809_;
}
else
{
lean_object* v_toApplyRulesConfig_2810_; lean_object* v_toBacktrackConfig_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_toApplyRulesConfig_2810_ = lean_ctor_get(v_cfg_2797_, 0);
v_toBacktrackConfig_2811_ = lean_ctor_get(v_toApplyRulesConfig_2810_, 0);
lean_inc_ref(v_toBacktrackConfig_2811_);
v___x_2812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2813_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2813_, 0, v_cfg_2797_);
lean_closure_set(v___x_2813_, 1, v_lemmas_2795_);
lean_closure_set(v___x_2813_, 2, v_ctx_2796_);
v___x_2814_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2811_, v___x_2812_, v___x_2813_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2815_, lean_object* v_ctx_2816_, lean_object* v_cfg_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2815_, v_ctx_2816_, v_cfg_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2825_, v___y_2827_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v_mvarId_2832_);
return v_res_2838_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_){
_start:
{
uint8_t v___x_2842_; 
v___x_2842_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2840_, v_x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_){
_start:
{
uint8_t v_res_2846_; lean_object* v_r_2847_; 
v_res_2846_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2843_, v_x_2844_, v_x_2845_);
lean_dec(v_x_2845_);
lean_dec_ref(v_x_2844_);
v_r_2847_ = lean_box(v_res_2846_);
return v_r_2847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2848_, lean_object* v_x_2849_, size_t v_x_2850_, lean_object* v_x_2851_){
_start:
{
uint8_t v___x_2852_; 
v___x_2852_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2849_, v_x_2850_, v_x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2853_, lean_object* v_x_2854_, lean_object* v_x_2855_, lean_object* v_x_2856_){
_start:
{
size_t v_x_2759__boxed_2857_; uint8_t v_res_2858_; lean_object* v_r_2859_; 
v_x_2759__boxed_2857_ = lean_unbox_usize(v_x_2855_);
lean_dec(v_x_2855_);
v_res_2858_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2853_, v_x_2854_, v_x_2759__boxed_2857_, v_x_2856_);
lean_dec(v_x_2856_);
lean_dec_ref(v_x_2854_);
v_r_2859_ = lean_box(v_res_2858_);
return v_r_2859_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2860_, lean_object* v_keys_2861_, lean_object* v_vals_2862_, lean_object* v_heq_2863_, lean_object* v_i_2864_, lean_object* v_k_2865_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2861_, v_i_2864_, v_k_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2867_, lean_object* v_keys_2868_, lean_object* v_vals_2869_, lean_object* v_heq_2870_, lean_object* v_i_2871_, lean_object* v_k_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2867_, v_keys_2868_, v_vals_2869_, v_heq_2870_, v_i_2871_, v_k_2872_);
lean_dec(v_k_2872_);
lean_dec_ref(v_vals_2869_);
lean_dec_ref(v_keys_2868_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2877_ = l_Lean_stringToMessageData(v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v_x_2886_);
return v_res_2892_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2895_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2896_ = l_Lean_Name_append(v___x_2895_, v___x_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2897_, lean_object* v_lemmas_2898_, lean_object* v_ctx_2899_, lean_object* v_goals_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_cfg_2906_; lean_object* v___x_2907_; 
v_cfg_2906_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2897_);
lean_inc(v_goals_2900_);
lean_inc_ref(v_cfg_2906_);
lean_inc_ref(v_ctx_2899_);
lean_inc(v_lemmas_2898_);
v___x_2907_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2898_, v_ctx_2899_, v_cfg_2906_, v_goals_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_dec_ref(v_cfg_2906_);
lean_dec(v_goals_2900_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
return v___x_2907_;
}
else
{
lean_object* v_a_2908_; lean_object* v___f_2909_; uint8_t v___y_2911_; lean_object* v___y_2912_; uint8_t v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v_a_2918_; uint8_t v___y_2931_; lean_object* v___y_2932_; uint8_t v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v_a_2938_; lean_object* v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2943_; uint8_t v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v_a_2948_; lean_object* v___y_2958_; uint8_t v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v_a_2965_; lean_object* v___y_2968_; uint8_t v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; uint8_t v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; uint8_t v___y_3010_; uint8_t v___x_3063_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
v___f_2909_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3063_ = l_Lean_Exception_isInterrupt(v_a_2908_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = l_Lean_Exception_isRuntime(v_a_2908_);
v___y_3010_ = v___x_3064_;
goto v___jp_3009_;
}
else
{
lean_dec(v_a_2908_);
v___y_3010_ = v___x_3063_;
goto v___jp_3009_;
}
v___jp_2910_:
{
lean_object* v___x_2919_; double v___x_2920_; double v___x_2921_; double v___x_2922_; double v___x_2923_; double v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2919_ = lean_io_mono_nanos_now();
v___x_2920_ = lean_float_of_nat(v___y_2917_);
v___x_2921_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2922_ = lean_float_div(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_float_of_nat(v___x_2919_);
v___x_2924_ = lean_float_div(v___x_2923_, v___x_2921_);
v___x_2925_ = lean_box_float(v___x_2922_);
v___x_2926_ = lean_box_float(v___x_2924_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v_a_2918_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2915_);
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2915_, v___y_2911_, v___y_2912_, v___y_2916_, v___y_2913_, v___y_2914_, v___f_2909_, v___x_2928_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_2929_;
}
v___jp_2930_:
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2938_);
v___y_2911_ = v___y_2931_;
v___y_2912_ = v___y_2932_;
v___y_2913_ = v___y_2933_;
v___y_2914_ = v___y_2934_;
v___y_2915_ = v___y_2935_;
v___y_2916_ = v___y_2936_;
v___y_2917_ = v___y_2937_;
v_a_2918_ = v___x_2939_;
goto v___jp_2910_;
}
v___jp_2940_:
{
lean_object* v___x_2949_; double v___x_2950_; double v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2949_ = lean_io_get_num_heartbeats();
v___x_2950_ = lean_float_of_nat(v___y_2941_);
v___x_2951_ = lean_float_of_nat(v___x_2949_);
v___x_2952_ = lean_box_float(v___x_2950_);
v___x_2953_ = lean_box_float(v___x_2951_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_a_2948_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
lean_inc_ref(v___y_2943_);
lean_inc(v___y_2946_);
v___x_2956_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2946_, v___y_2942_, v___y_2943_, v___y_2947_, v___y_2944_, v___y_2945_, v___f_2909_, v___x_2955_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_2956_;
}
v___jp_2957_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2965_);
v___y_2941_ = v___y_2958_;
v___y_2942_ = v___y_2959_;
v___y_2943_ = v___y_2960_;
v___y_2944_ = v___y_2961_;
v___y_2945_ = v___y_2962_;
v___y_2946_ = v___y_2963_;
v___y_2947_ = v___y_2964_;
v_a_2948_ = v___x_2966_;
goto v___jp_2940_;
}
v___jp_2967_:
{
lean_object* v___x_2975_; lean_object* v_a_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2975_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2904_);
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2978_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2974_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_io_mono_nanos_now();
v___x_2980_ = l_Lean_MVarId_exfalso(v___y_2968_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_a_2981_);
lean_ctor_set(v___x_2982_, 1, v___y_2970_);
v___x_2983_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2898_, v_ctx_2899_, v_cfg_2906_, v___x_2982_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 1);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
v___y_2911_ = v___y_2969_;
v___y_2912_ = v___y_2971_;
v___y_2913_ = v___y_2972_;
v___y_2914_ = v_a_2976_;
v___y_2915_ = v___y_2973_;
v___y_2916_ = v___y_2974_;
v___y_2917_ = v___x_2979_;
v_a_2918_ = v___x_2989_;
goto v___jp_2910_;
}
}
}
else
{
lean_object* v_a_2992_; 
v_a_2992_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2983_);
v___y_2931_ = v___y_2969_;
v___y_2932_ = v___y_2971_;
v___y_2933_ = v___y_2972_;
v___y_2934_ = v_a_2976_;
v___y_2935_ = v___y_2973_;
v___y_2936_ = v___y_2974_;
v___y_2937_ = v___x_2979_;
v_a_2938_ = v_a_2992_;
goto v___jp_2930_;
}
}
else
{
lean_object* v_a_2993_; 
lean_dec(v___y_2970_);
lean_dec_ref(v_cfg_2906_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
v_a_2993_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2993_);
lean_dec_ref(v___x_2980_);
v___y_2931_ = v___y_2969_;
v___y_2932_ = v___y_2971_;
v___y_2933_ = v___y_2972_;
v___y_2934_ = v_a_2976_;
v___y_2935_ = v___y_2973_;
v___y_2936_ = v___y_2974_;
v___y_2937_ = v___x_2979_;
v_a_2938_ = v_a_2993_;
goto v___jp_2930_;
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_io_get_num_heartbeats();
v___x_2995_ = l_Lean_MVarId_exfalso(v___y_2968_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2996_);
lean_ctor_set(v___x_2997_, 1, v___y_2970_);
v___x_2998_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2898_, v_ctx_2899_, v_cfg_2906_, v___x_2997_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 1);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
v___y_2941_ = v___x_2994_;
v___y_2942_ = v___y_2969_;
v___y_2943_ = v___y_2971_;
v___y_2944_ = v___y_2972_;
v___y_2945_ = v_a_2976_;
v___y_2946_ = v___y_2973_;
v___y_2947_ = v___y_2974_;
v_a_2948_ = v___x_3004_;
goto v___jp_2940_;
}
}
}
else
{
lean_object* v_a_3007_; 
v_a_3007_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_2998_);
v___y_2958_ = v___x_2994_;
v___y_2959_ = v___y_2969_;
v___y_2960_ = v___y_2971_;
v___y_2961_ = v___y_2972_;
v___y_2962_ = v_a_2976_;
v___y_2963_ = v___y_2973_;
v___y_2964_ = v___y_2974_;
v_a_2965_ = v_a_3007_;
goto v___jp_2957_;
}
}
else
{
lean_object* v_a_3008_; 
lean_dec(v___y_2970_);
lean_dec_ref(v_cfg_2906_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
v_a_3008_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_2995_);
v___y_2958_ = v___x_2994_;
v___y_2959_ = v___y_2969_;
v___y_2960_ = v___y_2971_;
v___y_2961_ = v___y_2972_;
v___y_2962_ = v_a_2976_;
v___y_2963_ = v___y_2973_;
v___y_2964_ = v___y_2974_;
v_a_2965_ = v_a_3008_;
goto v___jp_2957_;
}
}
}
v___jp_3009_:
{
if (v___y_3010_ == 0)
{
if (lean_obj_tag(v_goals_2900_) == 1)
{
lean_object* v_tail_3011_; 
v_tail_3011_ = lean_ctor_get(v_goals_2900_, 1);
lean_inc(v_tail_3011_);
if (lean_obj_tag(v_tail_3011_) == 0)
{
lean_object* v_toApplyRulesConfig_3012_; uint8_t v_exfalso_3013_; 
v_toApplyRulesConfig_3012_ = lean_ctor_get(v_cfg_2906_, 0);
lean_inc_ref(v_toApplyRulesConfig_3012_);
v_exfalso_3013_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3012_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_3012_);
if (v_exfalso_3013_ == 1)
{
lean_object* v_options_3014_; uint8_t v_hasTrace_3015_; 
lean_dec_ref(v___x_2907_);
v_options_3014_ = lean_ctor_get(v_a_2903_, 2);
v_hasTrace_3015_ = lean_ctor_get_uint8(v_options_3014_, sizeof(void*)*1);
if (v_hasTrace_3015_ == 0)
{
lean_object* v_head_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3034_; 
v_head_3016_ = lean_ctor_get(v_goals_2900_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_goals_2900_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v_goals_2900_, 1);
lean_dec(v_unused_3035_);
v___x_3018_ = v_goals_2900_;
v_isShared_3019_ = v_isSharedCheck_3034_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_head_3016_);
lean_dec(v_goals_2900_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3034_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_MVarId_exfalso(v_head_3016_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v_a_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3021_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_tail_3011_);
v___x_3023_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; 
v___x_3024_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2898_, v_ctx_2899_, v_cfg_2906_, v___x_3023_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_3024_;
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_3018_);
lean_dec_ref(v_cfg_2906_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
v_a_3026_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3020_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3020_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
else
{
lean_object* v_head_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3061_; 
v_head_3036_ = lean_ctor_get(v_goals_2900_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_goals_2900_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v_goals_2900_, 1);
lean_dec(v_unused_3062_);
v___x_3038_ = v_goals_2900_;
v_isShared_3039_ = v_isSharedCheck_3061_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_head_3036_);
lean_dec(v_goals_2900_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3061_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_inheritedTraceOptions_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_inheritedTraceOptions_3040_ = lean_ctor_get(v_a_2903_, 13);
v___x_3041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3042_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3043_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3044_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3040_, v_options_3014_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = l_Lean_trace_profiler;
v___x_3046_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_3014_, v___x_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_MVarId_exfalso(v_head_3036_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v_a_3048_);
v___x_3050_ = v___x_3038_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3048_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_tail_3011_);
v___x_3050_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2898_, v_ctx_2899_, v_cfg_2906_, v___x_3050_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_3051_;
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_del_object(v___x_3038_);
lean_dec_ref(v_cfg_2906_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
v_a_3053_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3047_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3047_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_del_object(v___x_3038_);
v___y_2968_ = v_head_3036_;
v___y_2969_ = v_exfalso_3013_;
v___y_2970_ = v_tail_3011_;
v___y_2971_ = v___x_3042_;
v___y_2972_ = v___x_3044_;
v___y_2973_ = v___x_3041_;
v___y_2974_ = v_options_3014_;
goto v___jp_2967_;
}
}
else
{
lean_del_object(v___x_3038_);
v___y_2968_ = v_head_3036_;
v___y_2969_ = v_exfalso_3013_;
v___y_2970_ = v_tail_3011_;
v___y_2971_ = v___x_3042_;
v___y_2972_ = v___x_3044_;
v___y_2973_ = v___x_3041_;
v___y_2974_ = v_options_3014_;
goto v___jp_2967_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2900_);
lean_dec_ref(v_cfg_2906_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
return v___x_2907_;
}
}
else
{
lean_dec_ref(v_goals_2900_);
lean_dec(v_tail_3011_);
lean_dec_ref(v_cfg_2906_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
return v___x_2907_;
}
}
else
{
lean_dec_ref(v_cfg_2906_);
lean_dec(v_goals_2900_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
return v___x_2907_;
}
}
else
{
lean_dec_ref(v_cfg_2906_);
lean_dec(v_goals_2900_);
lean_dec_ref(v_ctx_2899_);
lean_dec(v_lemmas_2898_);
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3065_, lean_object* v_lemmas_3066_, lean_object* v_ctx_3067_, lean_object* v_goals_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3065_, v_lemmas_3066_, v_ctx_3067_, v_goals_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
if (lean_obj_tag(v_x_3075_) == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = l_List_reverse___redArg(v_x_3076_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
else
{
lean_object* v_head_3084_; lean_object* v_tail_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3108_; 
v_head_3084_ = lean_ctor_get(v_x_3075_, 0);
v_tail_3085_ = lean_ctor_get(v_x_3075_, 1);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_x_3075_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3087_ = v_x_3075_;
v_isShared_3088_ = v_isSharedCheck_3108_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_tail_3085_);
lean_inc(v_head_3084_);
lean_dec(v_x_3075_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3108_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Expr_applySymm(v_head_3084_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref(v___x_3089_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v_x_3076_);
lean_ctor_set(v___x_3087_, 0, v_a_3090_);
v___x_3092_ = v___x_3087_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3090_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_x_3076_);
v___x_3092_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
v_x_3075_ = v_tail_3085_;
v_x_3076_ = v___x_3092_;
goto _start;
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_3087_);
v_a_3095_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3097_ = v___x_3089_;
v_isShared_3098_ = v_isSharedCheck_3107_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3089_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3107_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint8_t v___y_3100_; uint8_t v___x_3105_; 
v___x_3105_ = l_Lean_Exception_isInterrupt(v_a_3095_);
if (v___x_3105_ == 0)
{
uint8_t v___x_3106_; 
lean_inc(v_a_3095_);
v___x_3106_ = l_Lean_Exception_isRuntime(v_a_3095_);
v___y_3100_ = v___x_3106_;
goto v___jp_3099_;
}
else
{
v___y_3100_ = v___x_3105_;
goto v___jp_3099_;
}
v___jp_3099_:
{
if (v___y_3100_ == 0)
{
lean_del_object(v___x_3097_);
lean_dec(v_a_3095_);
v_x_3075_ = v_tail_3085_;
goto _start;
}
else
{
lean_object* v___x_3103_; 
lean_dec(v_tail_3085_);
lean_dec(v_x_3076_);
if (v_isShared_3098_ == 0)
{
v___x_3103_ = v___x_3097_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3095_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3109_, v_x_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3117_, lean_object* v_hyps_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_){
_start:
{
if (v_symm_3117_ == 0)
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_hyps_3118_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_box(0);
lean_inc(v_hyps_3118_);
v___x_3126_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3118_, v___x_3125_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3135_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3135_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3131_ = l_List_appendTR___redArg(v_hyps_3118_, v_a_3127_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3131_);
v___x_3133_ = v___x_3129_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_dec(v_hyps_3118_);
return v___x_3126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3136_, lean_object* v_hyps_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
uint8_t v_symm_boxed_3143_; lean_object* v_res_3144_; 
v_symm_boxed_3143_ = lean_unbox(v_symm_3136_);
v_res_3144_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3143_, v_hyps_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3145_, size_t v_sz_3146_, size_t v_i_3147_, lean_object* v_b_3148_){
_start:
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_usize_dec_lt(v_i_3147_, v_sz_3146_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_b_3148_);
return v___x_3151_;
}
else
{
lean_object* v_snd_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3170_; 
v_snd_3152_ = lean_ctor_get(v_b_3148_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_b_3148_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v_b_3148_, 0);
lean_dec(v_unused_3171_);
v___x_3154_ = v_b_3148_;
v_isShared_3155_ = v_isSharedCheck_3170_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snd_3152_);
lean_dec(v_b_3148_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3170_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v_a_3158_; lean_object* v_a_3165_; 
v___x_3156_ = lean_box(0);
v_a_3165_ = lean_array_uget_borrowed(v_as_3145_, v_i_3147_);
if (lean_obj_tag(v_a_3165_) == 0)
{
v_a_3158_ = v_snd_3152_;
goto v___jp_3157_;
}
else
{
lean_object* v_val_3166_; uint8_t v___x_3167_; 
v_val_3166_ = lean_ctor_get(v_a_3165_, 0);
v___x_3167_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
lean_inc(v_val_3166_);
v___x_3168_ = l_Lean_LocalDecl_toExpr(v_val_3166_);
v___x_3169_ = lean_array_push(v_snd_3152_, v___x_3168_);
v_a_3158_ = v___x_3169_;
goto v___jp_3157_;
}
else
{
v_a_3158_ = v_snd_3152_;
goto v___jp_3157_;
}
}
v___jp_3157_:
{
lean_object* v___x_3160_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v_a_3158_);
lean_ctor_set(v___x_3154_, 0, v___x_3156_);
v___x_3160_ = v___x_3154_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_a_3158_);
v___x_3160_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
size_t v___x_3161_; size_t v___x_3162_; 
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3147_, v___x_3161_);
v_i_3147_ = v___x_3162_;
v_b_3148_ = v___x_3160_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3172_, lean_object* v_sz_3173_, lean_object* v_i_3174_, lean_object* v_b_3175_, lean_object* v___y_3176_){
_start:
{
size_t v_sz_boxed_3177_; size_t v_i_boxed_3178_; lean_object* v_res_3179_; 
v_sz_boxed_3177_ = lean_unbox_usize(v_sz_3173_);
lean_dec(v_sz_3173_);
v_i_boxed_3178_ = lean_unbox_usize(v_i_3174_);
lean_dec(v_i_3174_);
v_res_3179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3172_, v_sz_boxed_3177_, v_i_boxed_3178_, v_b_3175_);
lean_dec_ref(v_as_3172_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3180_, size_t v_sz_3181_, size_t v_i_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v___x_3191_; 
v___x_3191_ = lean_usize_dec_lt(v_i_3182_, v_sz_3181_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_b_3183_);
return v___x_3192_;
}
else
{
lean_object* v_snd_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3211_; 
v_snd_3193_ = lean_ctor_get(v_b_3183_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_b_3183_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; 
v_unused_3212_ = lean_ctor_get(v_b_3183_, 0);
lean_dec(v_unused_3212_);
v___x_3195_ = v_b_3183_;
v_isShared_3196_ = v_isSharedCheck_3211_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_snd_3193_);
lean_dec(v_b_3183_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3211_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v_a_3199_; lean_object* v_a_3206_; 
v___x_3197_ = lean_box(0);
v_a_3206_ = lean_array_uget_borrowed(v_as_3180_, v_i_3182_);
if (lean_obj_tag(v_a_3206_) == 0)
{
v_a_3199_ = v_snd_3193_;
goto v___jp_3198_;
}
else
{
lean_object* v_val_3207_; uint8_t v___x_3208_; 
v_val_3207_ = lean_ctor_get(v_a_3206_, 0);
v___x_3208_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_inc(v_val_3207_);
v___x_3209_ = l_Lean_LocalDecl_toExpr(v_val_3207_);
v___x_3210_ = lean_array_push(v_snd_3193_, v___x_3209_);
v_a_3199_ = v___x_3210_;
goto v___jp_3198_;
}
else
{
v_a_3199_ = v_snd_3193_;
goto v___jp_3198_;
}
}
v___jp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v_a_3199_);
lean_ctor_set(v___x_3195_, 0, v___x_3197_);
v___x_3201_ = v___x_3195_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_a_3199_);
v___x_3201_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
size_t v___x_3202_; size_t v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = ((size_t)1ULL);
v___x_3203_ = lean_usize_add(v_i_3182_, v___x_3202_);
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3180_, v_sz_3181_, v___x_3203_, v___x_3201_);
return v___x_3204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3213_, lean_object* v_sz_3214_, lean_object* v_i_3215_, lean_object* v_b_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
size_t v_sz_boxed_3224_; size_t v_i_boxed_3225_; lean_object* v_res_3226_; 
v_sz_boxed_3224_ = lean_unbox_usize(v_sz_3214_);
lean_dec(v_sz_3214_);
v_i_boxed_3225_ = lean_unbox_usize(v_i_3215_);
lean_dec(v_i_3215_);
v_res_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3213_, v_sz_boxed_3224_, v_i_boxed_3225_, v_b_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec_ref(v_as_3213_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3227_, size_t v_sz_3228_, size_t v_i_3229_, lean_object* v_b_3230_){
_start:
{
uint8_t v___x_3232_; 
v___x_3232_ = lean_usize_dec_lt(v_i_3229_, v_sz_3228_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3233_, 0, v_b_3230_);
return v___x_3233_;
}
else
{
lean_object* v_snd_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3252_; 
v_snd_3234_ = lean_ctor_get(v_b_3230_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_b_3230_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v_b_3230_, 0);
lean_dec(v_unused_3253_);
v___x_3236_ = v_b_3230_;
v_isShared_3237_ = v_isSharedCheck_3252_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_snd_3234_);
lean_dec(v_b_3230_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3252_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v_a_3240_; lean_object* v_a_3247_; 
v___x_3238_ = lean_box(0);
v_a_3247_ = lean_array_uget_borrowed(v_as_3227_, v_i_3229_);
if (lean_obj_tag(v_a_3247_) == 0)
{
v_a_3240_ = v_snd_3234_;
goto v___jp_3239_;
}
else
{
lean_object* v_val_3248_; uint8_t v___x_3249_; 
v_val_3248_ = lean_ctor_get(v_a_3247_, 0);
v___x_3249_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_inc(v_val_3248_);
v___x_3250_ = l_Lean_LocalDecl_toExpr(v_val_3248_);
v___x_3251_ = lean_array_push(v_snd_3234_, v___x_3250_);
v_a_3240_ = v___x_3251_;
goto v___jp_3239_;
}
else
{
v_a_3240_ = v_snd_3234_;
goto v___jp_3239_;
}
}
v___jp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 1, v_a_3240_);
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3242_ = v___x_3236_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_a_3240_);
v___x_3242_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
size_t v___x_3243_; size_t v___x_3244_; 
v___x_3243_ = ((size_t)1ULL);
v___x_3244_ = lean_usize_add(v_i_3229_, v___x_3243_);
v_i_3229_ = v___x_3244_;
v_b_3230_ = v___x_3242_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3254_, lean_object* v_sz_3255_, lean_object* v_i_3256_, lean_object* v_b_3257_, lean_object* v___y_3258_){
_start:
{
size_t v_sz_boxed_3259_; size_t v_i_boxed_3260_; lean_object* v_res_3261_; 
v_sz_boxed_3259_ = lean_unbox_usize(v_sz_3255_);
lean_dec(v_sz_3255_);
v_i_boxed_3260_ = lean_unbox_usize(v_i_3256_);
lean_dec(v_i_3256_);
v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3254_, v_sz_boxed_3259_, v_i_boxed_3260_, v_b_3257_);
lean_dec_ref(v_as_3254_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3262_, size_t v_sz_3263_, size_t v_i_3264_, lean_object* v_b_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
uint8_t v___x_3273_; 
v___x_3273_ = lean_usize_dec_lt(v_i_3264_, v_sz_3263_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_b_3265_);
return v___x_3274_;
}
else
{
lean_object* v_snd_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3293_; 
v_snd_3275_ = lean_ctor_get(v_b_3265_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_b_3265_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v_b_3265_, 0);
lean_dec(v_unused_3294_);
v___x_3277_ = v_b_3265_;
v_isShared_3278_ = v_isSharedCheck_3293_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_snd_3275_);
lean_dec(v_b_3265_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3293_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v_a_3281_; lean_object* v_a_3288_; 
v___x_3279_ = lean_box(0);
v_a_3288_ = lean_array_uget_borrowed(v_as_3262_, v_i_3264_);
if (lean_obj_tag(v_a_3288_) == 0)
{
v_a_3281_ = v_snd_3275_;
goto v___jp_3280_;
}
else
{
lean_object* v_val_3289_; uint8_t v___x_3290_; 
v_val_3289_ = lean_ctor_get(v_a_3288_, 0);
v___x_3290_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_inc(v_val_3289_);
v___x_3291_ = l_Lean_LocalDecl_toExpr(v_val_3289_);
v___x_3292_ = lean_array_push(v_snd_3275_, v___x_3291_);
v_a_3281_ = v___x_3292_;
goto v___jp_3280_;
}
else
{
v_a_3281_ = v_snd_3275_;
goto v___jp_3280_;
}
}
v___jp_3280_:
{
lean_object* v___x_3283_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v_a_3281_);
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3283_ = v___x_3277_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_a_3281_);
v___x_3283_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
size_t v___x_3284_; size_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = ((size_t)1ULL);
v___x_3285_ = lean_usize_add(v_i_3264_, v___x_3284_);
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3262_, v_sz_3263_, v___x_3285_, v___x_3283_);
return v___x_3286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3295_, lean_object* v_sz_3296_, lean_object* v_i_3297_, lean_object* v_b_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
size_t v_sz_boxed_3306_; size_t v_i_boxed_3307_; lean_object* v_res_3308_; 
v_sz_boxed_3306_ = lean_unbox_usize(v_sz_3296_);
lean_dec(v_sz_3296_);
v_i_boxed_3307_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3295_, v_sz_boxed_3306_, v_i_boxed_3307_, v_b_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v_as_3295_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3309_, lean_object* v_n_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
if (lean_obj_tag(v_n_3310_) == 0)
{
lean_object* v_cs_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; size_t v_sz_3322_; size_t v___x_3323_; lean_object* v___x_3324_; 
v_cs_3319_ = lean_ctor_get(v_n_3310_, 0);
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v_b_3311_);
v_sz_3322_ = lean_array_size(v_cs_3319_);
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3309_, v_cs_3319_, v_sz_3322_, v___x_3323_, v___x_3321_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3339_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3339_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3339_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_fst_3329_; 
v_fst_3329_ = lean_ctor_get(v_a_3325_, 0);
if (lean_obj_tag(v_fst_3329_) == 0)
{
lean_object* v_snd_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
v_snd_3330_ = lean_ctor_get(v_a_3325_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_a_3325_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_snd_3330_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3331_);
v___x_3333_ = v___x_3327_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
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
lean_inc_ref(v_fst_3329_);
lean_dec(v_a_3325_);
v_val_3335_ = lean_ctor_get(v_fst_3329_, 0);
lean_inc(v_val_3335_);
lean_dec_ref(v_fst_3329_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v_val_3335_);
v___x_3337_ = v___x_3327_;
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
v_a_3340_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3324_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3324_);
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
else
{
lean_object* v_vs_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; size_t v_sz_3351_; size_t v___x_3352_; lean_object* v___x_3353_; 
v_vs_3348_ = lean_ctor_get(v_n_3310_, 0);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v_b_3311_);
v_sz_3351_ = lean_array_size(v_vs_3348_);
v___x_3352_ = ((size_t)0ULL);
v___x_3353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3348_, v_sz_3351_, v___x_3352_, v___x_3350_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3368_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3368_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3368_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_fst_3358_; 
v_fst_3358_ = lean_ctor_get(v_a_3354_, 0);
if (lean_obj_tag(v_fst_3358_) == 0)
{
lean_object* v_snd_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v_snd_3359_ = lean_ctor_get(v_a_3354_, 1);
lean_inc(v_snd_3359_);
lean_dec(v_a_3354_);
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_snd_3359_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3360_);
v___x_3362_ = v___x_3356_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
else
{
lean_object* v_val_3364_; lean_object* v___x_3366_; 
lean_inc_ref(v_fst_3358_);
lean_dec(v_a_3354_);
v_val_3364_ = lean_ctor_get(v_fst_3358_, 0);
lean_inc(v_val_3364_);
lean_dec_ref(v_fst_3358_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v_val_3364_);
v___x_3366_ = v___x_3356_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_val_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_a_3369_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3353_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3353_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3377_, lean_object* v_as_3378_, size_t v_sz_3379_, size_t v_i_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
uint8_t v___x_3389_; 
v___x_3389_ = lean_usize_dec_lt(v_i_3380_, v_sz_3379_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v_b_3381_);
return v___x_3390_;
}
else
{
lean_object* v_snd_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3425_; 
v_snd_3391_ = lean_ctor_get(v_b_3381_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_b_3381_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v_b_3381_, 0);
lean_dec(v_unused_3426_);
v___x_3393_ = v_b_3381_;
v_isShared_3394_ = v_isSharedCheck_3425_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_snd_3391_);
lean_dec(v_b_3381_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3425_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_a_3395_; lean_object* v___x_3396_; 
v_a_3395_ = lean_array_uget_borrowed(v_as_3378_, v_i_3380_);
lean_inc(v_snd_3391_);
v___x_3396_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3377_, v_a_3395_, v_snd_3391_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3416_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3416_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3416_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
if (lean_obj_tag(v_a_3397_) == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3401_, 0, v_a_3397_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3401_);
v___x_3403_ = v___x_3393_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_snd_3391_);
v___x_3403_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3405_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3403_);
v___x_3405_ = v___x_3399_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
lean_del_object(v___x_3399_);
lean_dec(v_snd_3391_);
v_a_3408_ = lean_ctor_get(v_a_3397_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v_a_3397_);
v___x_3409_ = lean_box(0);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v_a_3408_);
lean_ctor_set(v___x_3393_, 0, v___x_3409_);
v___x_3411_ = v___x_3393_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_a_3408_);
v___x_3411_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
size_t v___x_3412_; size_t v___x_3413_; 
v___x_3412_ = ((size_t)1ULL);
v___x_3413_ = lean_usize_add(v_i_3380_, v___x_3412_);
v_i_3380_ = v___x_3413_;
v_b_3381_ = v___x_3411_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_del_object(v___x_3393_);
lean_dec(v_snd_3391_);
v_a_3417_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3396_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3396_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3427_, lean_object* v_as_3428_, lean_object* v_sz_3429_, lean_object* v_i_3430_, lean_object* v_b_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
size_t v_sz_boxed_3439_; size_t v_i_boxed_3440_; lean_object* v_res_3441_; 
v_sz_boxed_3439_ = lean_unbox_usize(v_sz_3429_);
lean_dec(v_sz_3429_);
v_i_boxed_3440_ = lean_unbox_usize(v_i_3430_);
lean_dec(v_i_3430_);
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3427_, v_as_3428_, v_sz_boxed_3439_, v_i_boxed_3440_, v_b_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_as_3428_);
lean_dec_ref(v_init_3427_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3442_, lean_object* v_n_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3442_, v_n_3443_, v_b_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v_n_3443_);
lean_dec_ref(v_init_3442_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3453_, lean_object* v_init_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_root_3462_; lean_object* v_tail_3463_; lean_object* v___x_3464_; 
v_root_3462_ = lean_ctor_get(v_t_3453_, 0);
v_tail_3463_ = lean_ctor_get(v_t_3453_, 1);
lean_inc_ref(v_init_3454_);
v___x_3464_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3454_, v_root_3462_, v_init_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec_ref(v_init_3454_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3501_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3501_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3501_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
if (lean_obj_tag(v_a_3465_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; 
v_a_3469_ = lean_ctor_get(v_a_3465_, 0);
lean_inc(v_a_3469_);
lean_dec_ref(v_a_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v_a_3469_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; size_t v_sz_3476_; size_t v___x_3477_; lean_object* v___x_3478_; 
lean_del_object(v___x_3467_);
v_a_3473_ = lean_ctor_get(v_a_3465_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v_a_3465_);
v___x_3474_ = lean_box(0);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v_a_3473_);
v_sz_3476_ = lean_array_size(v_tail_3463_);
v___x_3477_ = ((size_t)0ULL);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3463_, v_sz_3476_, v___x_3477_, v___x_3475_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3492_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3492_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3492_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_fst_3483_; 
v_fst_3483_ = lean_ctor_get(v_a_3479_, 0);
if (lean_obj_tag(v_fst_3483_) == 0)
{
lean_object* v_snd_3484_; lean_object* v___x_3486_; 
v_snd_3484_ = lean_ctor_get(v_a_3479_, 1);
lean_inc(v_snd_3484_);
lean_dec(v_a_3479_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v_snd_3484_);
v___x_3486_ = v___x_3481_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_snd_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
else
{
lean_object* v_val_3488_; lean_object* v___x_3490_; 
lean_inc_ref(v_fst_3483_);
lean_dec(v_a_3479_);
v_val_3488_ = lean_ctor_get(v_fst_3483_, 0);
lean_inc(v_val_3488_);
lean_dec_ref(v_fst_3483_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v_val_3488_);
v___x_3490_ = v___x_3481_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_val_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
v_a_3493_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3478_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3478_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3464_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3464_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3510_, lean_object* v_init_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3510_, v_init_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v_t_3510_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_lctx_3529_; lean_object* v_decls_3530_; lean_object* v_hs_3531_; lean_object* v___x_3532_; 
v_lctx_3529_ = lean_ctor_get(v___y_3524_, 2);
v_decls_3530_ = lean_ctor_get(v_lctx_3529_, 1);
v_hs_3531_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3532_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3530_, v_hs_3531_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3541_, lean_object* v_cfg_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
if (v_only_3541_ == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_toApplyRulesConfig_3551_; lean_object* v_a_3552_; uint8_t v_symm_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_toApplyRulesConfig_3551_ = lean_ctor_get(v_cfg_3542_, 0);
v_a_3552_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3552_);
lean_dec_ref(v___x_3550_);
v_symm_3553_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3551_, sizeof(void*)*2 + 1);
v___x_3554_ = lean_array_to_list(v_a_3552_);
v___x_3555_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3553_, v___x_3554_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3555_;
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
v_a_3556_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3550_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3550_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_box(0);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3566_, lean_object* v_cfg_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v_only_boxed_3575_; lean_object* v_res_3576_; 
v_only_boxed_3575_ = lean_unbox(v_only_3566_);
v_res_3576_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3575_, v_cfg_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_cfg_3567_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3577_, lean_object* v_lemmas_3578_, uint8_t v_only_3579_, lean_object* v_g_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_toApplyRulesConfig_3586_; uint8_t v_intro_3587_; uint8_t v_constructor_3588_; uint8_t v_suggestions_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3602_; 
v_toApplyRulesConfig_3586_ = lean_ctor_get(v_cfg_3577_, 0);
v_intro_3587_ = lean_ctor_get_uint8(v_cfg_3577_, sizeof(void*)*1 + 1);
v_constructor_3588_ = lean_ctor_get_uint8(v_cfg_3577_, sizeof(void*)*1 + 2);
v_suggestions_3589_ = lean_ctor_get_uint8(v_cfg_3577_, sizeof(void*)*1 + 3);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_cfg_3577_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3591_ = v_cfg_3577_;
v_isShared_3592_ = v_isSharedCheck_3602_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_toApplyRulesConfig_3586_);
lean_dec(v_cfg_3577_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3602_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v_ctx_3594_; uint8_t v___x_3595_; lean_object* v___x_3597_; 
v___x_3593_ = lean_box(v_only_3579_);
v_ctx_3594_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3594_, 0, v___x_3593_);
v___x_3595_ = 0;
if (v_isShared_3592_ == 0)
{
v___x_3597_ = v___x_3591_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_toApplyRulesConfig_3586_);
lean_ctor_set_uint8(v_reuseFailAlloc_3601_, sizeof(void*)*1 + 1, v_intro_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3601_, sizeof(void*)*1 + 2, v_constructor_3588_);
lean_ctor_set_uint8(v_reuseFailAlloc_3601_, sizeof(void*)*1 + 3, v_suggestions_3589_);
v___x_3597_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*1, v___x_3595_);
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3599_, 0, v_g_3580_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3597_, v_lemmas_3578_, v_ctx_3594_, v___x_3599_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
return v___x_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3603_, lean_object* v_lemmas_3604_, lean_object* v_only_3605_, lean_object* v_g_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
uint8_t v_only_boxed_3612_; lean_object* v_res_3613_; 
v_only_boxed_3612_ = lean_unbox(v_only_3605_);
v_res_3613_ = l_Lean_MVarId_applyRules(v_cfg_3603_, v_lemmas_3604_, v_only_boxed_3612_, v_g_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3614_, size_t v_sz_3615_, size_t v_i_3616_, lean_object* v_b_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3614_, v_sz_3615_, v_i_3616_, v_b_3617_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3626_, lean_object* v_sz_3627_, lean_object* v_i_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3627_);
lean_dec(v_sz_3627_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3628_);
lean_dec(v_i_3628_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3626_, v_sz_boxed_3637_, v_i_boxed_3638_, v_b_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v_as_3626_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3640_, size_t v_sz_3641_, size_t v_i_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3640_, v_sz_3641_, v_i_3642_, v_b_3643_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3652_, lean_object* v_sz_3653_, lean_object* v_i_3654_, lean_object* v_b_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
size_t v_sz_boxed_3663_; size_t v_i_boxed_3664_; lean_object* v_res_3665_; 
v_sz_boxed_3663_ = lean_unbox_usize(v_sz_3653_);
lean_dec(v_sz_3653_);
v_i_boxed_3664_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_res_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3652_, v_sz_boxed_3663_, v_i_boxed_3664_, v_b_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec_ref(v_as_3652_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v___x_3674_; uint8_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = lean_box(0);
v___x_3675_ = 1;
v___x_3676_ = l_Lean_Elab_Term_elabTerm(v_t_3666_, v___x_3674_, v___x_3675_, v___x_3675_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_ref_3691_; uint8_t v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_ref_3691_ = lean_ctor_get(v___y_3688_, 5);
v___x_3692_ = 0;
v___x_3693_ = l_Lean_SourceInfo_fromRef(v_ref_3691_, v___x_3692_);
v___x_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3700_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3701_, lean_object* v_x_3702_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
uint8_t v___x_3703_; 
v___x_3703_ = 0;
return v___x_3703_;
}
else
{
lean_object* v_head_3704_; lean_object* v_tail_3705_; uint8_t v___x_3706_; 
v_head_3704_ = lean_ctor_get(v_x_3702_, 0);
v_tail_3705_ = lean_ctor_get(v_x_3702_, 1);
v___x_3706_ = lean_expr_eqv(v_a_3701_, v_head_3704_);
if (v___x_3706_ == 0)
{
v_x_3702_ = v_tail_3705_;
goto _start;
}
else
{
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3708_, lean_object* v_x_3709_){
_start:
{
uint8_t v_res_3710_; lean_object* v_r_3711_; 
v_res_3710_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3708_, v_x_3709_);
lean_dec(v_x_3709_);
lean_dec_ref(v_a_3708_);
v_r_3711_ = lean_box(v_res_3710_);
return v_r_3711_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3712_, lean_object* v_x_3713_){
_start:
{
uint8_t v___x_3714_; 
v___x_3714_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3713_, v_ys_3712_);
if (v___x_3714_ == 0)
{
uint8_t v___x_3715_; 
v___x_3715_ = 1;
return v___x_3715_;
}
else
{
uint8_t v___x_3716_; 
v___x_3716_ = 0;
return v___x_3716_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3717_, lean_object* v_x_3718_){
_start:
{
uint8_t v_res_3719_; lean_object* v_r_3720_; 
v_res_3719_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3717_, v_x_3718_);
lean_dec_ref(v_x_3718_);
lean_dec(v_ys_3717_);
v_r_3720_ = lean_box(v_res_3719_);
return v_r_3720_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3721_, lean_object* v_ys_3722_){
_start:
{
lean_object* v___f_3723_; lean_object* v___x_3724_; 
v___f_3723_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3723_, 0, v_ys_3722_);
v___x_3724_ = l_List_filter___redArg(v___f_3723_, v_xs_3721_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3725_, lean_object* v_x_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
if (lean_obj_tag(v_x_3725_) == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = l_List_reverse___redArg(v_x_3726_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
else
{
lean_object* v_head_3736_; lean_object* v_tail_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3755_; 
v_head_3736_ = lean_ctor_get(v_x_3725_, 0);
v_tail_3737_ = lean_ctor_get(v_x_3725_, 1);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_x_3725_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3739_ = v_x_3725_;
v_isShared_3740_ = v_isSharedCheck_3755_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_tail_3737_);
lean_inc(v_head_3736_);
lean_dec(v_x_3725_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3755_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; 
v___x_3741_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3736_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
lean_dec_ref(v___x_3741_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 1, v_x_3726_);
lean_ctor_set(v___x_3739_, 0, v_a_3742_);
v___x_3744_ = v___x_3739_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3742_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_x_3726_);
v___x_3744_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
v_x_3725_ = v_tail_3737_;
v_x_3726_ = v___x_3744_;
goto _start;
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_del_object(v___x_3739_);
lean_dec(v_tail_3737_);
lean_dec(v_x_3726_);
v_a_3747_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3741_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3741_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3756_, v_x_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3766_, uint8_t v_noDefaults_3767_, uint8_t v_star_3768_, lean_object* v_cfg_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
if (v_noDefaults_3767_ == 0)
{
goto v___jp_3777_;
}
else
{
if (v_star_3768_ == 0)
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
lean_dec(v_remove_3766_);
v___x_3796_ = lean_box(0);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
else
{
goto v___jp_3777_;
}
}
v___jp_3777_:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = lean_box(0);
v___x_3781_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3766_, v___x_3780_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_toApplyRulesConfig_3782_; lean_object* v_a_3783_; uint8_t v_symm_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_toApplyRulesConfig_3782_ = lean_ctor_get(v_cfg_3769_, 0);
v_a_3783_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3783_);
lean_dec_ref(v___x_3781_);
v_symm_3784_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3782_, sizeof(void*)*2 + 1);
v___x_3785_ = lean_array_to_list(v_a_3779_);
v___x_3786_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3785_, v_a_3783_);
v___x_3787_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3784_, v___x_3786_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
return v___x_3787_;
}
else
{
lean_dec(v_a_3779_);
return v___x_3781_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec(v_remove_3766_);
v_a_3788_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3778_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3778_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3798_, lean_object* v_noDefaults_3799_, lean_object* v_star_3800_, lean_object* v_cfg_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v_noDefaults_boxed_3809_; uint8_t v_star_boxed_3810_; lean_object* v_res_3811_; 
v_noDefaults_boxed_3809_ = lean_unbox(v_noDefaults_3799_);
v_star_boxed_3810_ = lean_unbox(v_star_3800_);
v_res_3811_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3798_, v_noDefaults_boxed_3809_, v_star_boxed_3810_, v_cfg_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v_cfg_3801_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3812_, size_t v_i_3813_, size_t v_stop_3814_, lean_object* v_b_3815_){
_start:
{
uint8_t v___x_3816_; 
v___x_3816_ = lean_usize_dec_eq(v_i_3813_, v_stop_3814_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; 
v___x_3817_ = lean_array_uget_borrowed(v_as_3812_, v_i_3813_);
v___x_3818_ = l_Array_append___redArg(v_b_3815_, v___x_3817_);
v___x_3819_ = ((size_t)1ULL);
v___x_3820_ = lean_usize_add(v_i_3813_, v___x_3819_);
v_i_3813_ = v___x_3820_;
v_b_3815_ = v___x_3818_;
goto _start;
}
else
{
return v_b_3815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3822_, lean_object* v_i_3823_, lean_object* v_stop_3824_, lean_object* v_b_3825_){
_start:
{
size_t v_i_boxed_3826_; size_t v_stop_boxed_3827_; lean_object* v_res_3828_; 
v_i_boxed_3826_ = lean_unbox_usize(v_i_3823_);
lean_dec(v_i_3823_);
v_stop_boxed_3827_ = lean_unbox_usize(v_stop_3824_);
lean_dec(v_stop_3824_);
v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3822_, v_i_boxed_3826_, v_stop_boxed_3827_, v_b_3825_);
lean_dec_ref(v_as_3822_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3829_, lean_object* v_a_3830_){
_start:
{
if (lean_obj_tag(v_a_3829_) == 0)
{
lean_object* v___x_3831_; 
v___x_3831_ = l_List_reverse___redArg(v_a_3830_);
return v___x_3831_;
}
else
{
lean_object* v_head_3832_; lean_object* v_tail_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3842_; 
v_head_3832_ = lean_ctor_get(v_a_3829_, 0);
v_tail_3833_ = lean_ctor_get(v_a_3829_, 1);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_a_3829_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3835_ = v_a_3829_;
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_tail_3833_);
lean_inc(v_head_3832_);
lean_dec(v_a_3829_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3837_, 0, v_head_3832_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 1, v_a_3830_);
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_a_3830_);
v___x_3839_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
v_a_3829_ = v_tail_3833_;
v_a_3830_ = v___x_3839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3843_, size_t v_i_3844_, lean_object* v_bs_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
uint8_t v___x_3849_; 
v___x_3849_ = lean_usize_dec_lt(v_i_3844_, v_sz_3843_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v_bs_3845_);
return v___x_3850_;
}
else
{
lean_object* v_v_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_v_3851_ = lean_array_uget_borrowed(v_bs_3845_, v_i_3844_);
v___x_3852_ = l_Lean_Syntax_getId(v_v_3851_);
v___x_3853_ = l_Lean_labelled(v___x_3852_, v___y_3846_, v___y_3847_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v_bs_x27_3856_; size_t v___x_3857_; size_t v___x_3858_; lean_object* v___x_3859_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3853_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v_bs_x27_3856_ = lean_array_uset(v_bs_3845_, v_i_3844_, v___x_3855_);
v___x_3857_ = ((size_t)1ULL);
v___x_3858_ = lean_usize_add(v_i_3844_, v___x_3857_);
v___x_3859_ = lean_array_uset(v_bs_x27_3856_, v_i_3844_, v_a_3854_);
v_i_3844_ = v___x_3858_;
v_bs_3845_ = v___x_3859_;
goto _start;
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_bs_3845_);
v_a_3861_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3853_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3853_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3869_, lean_object* v_i_3870_, lean_object* v_bs_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3869_);
lean_dec(v_sz_3869_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3870_);
lean_dec(v_i_3870_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3875_, v_i_boxed_3876_, v_bs_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3878_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
if (lean_obj_tag(v_a_3896_) == 0)
{
lean_object* v___x_3898_; 
v___x_3898_ = l_List_reverse___redArg(v_a_3897_);
return v___x_3898_;
}
else
{
lean_object* v_head_3899_; lean_object* v_tail_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3909_; 
v_head_3899_ = lean_ctor_get(v_a_3896_, 0);
v_tail_3900_ = lean_ctor_get(v_a_3896_, 1);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3896_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3902_ = v_a_3896_;
v_isShared_3903_ = v_isSharedCheck_3909_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_tail_3900_);
lean_inc(v_head_3899_);
lean_dec(v_a_3896_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3909_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___f_3904_; lean_object* v___x_3906_; 
v___f_3904_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3904_, 0, v_head_3899_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 1, v_a_3897_);
lean_ctor_set(v___x_3902_, 0, v___f_3904_);
v___x_3906_ = v___x_3902_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___f_3904_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_a_3897_);
v___x_3906_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
v_a_3896_ = v_tail_3900_;
v_a_3897_ = v___x_3906_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3912_ = l_Lean_stringToMessageData(v___x_3911_);
return v___x_3912_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3915_ = l_String_toRawSubstring_x27(v___x_3914_);
return v___x_3915_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3920_ = l_String_toRawSubstring_x27(v___x_3919_);
return v___x_3920_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3925_ = l_String_toRawSubstring_x27(v___x_3924_);
return v___x_3925_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3930_ = l_String_toRawSubstring_x27(v___x_3929_);
return v___x_3930_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3962_, uint8_t v_star_3963_, lean_object* v_add_3964_, lean_object* v_remove_3965_, lean_object* v_use_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___f_3997_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; 
v___x_3995_ = lean_box(v_noDefaults_3962_);
v___x_3996_ = lean_box(v_star_3963_);
lean_inc(v_remove_3965_);
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3997_, 0, v_remove_3965_);
lean_closure_set(v___f_3997_, 1, v___x_3995_);
lean_closure_set(v___f_3997_, 2, v___x_3996_);
if (v_star_3963_ == 0)
{
v___y_4014_ = v_a_3967_;
v___y_4015_ = v_a_3968_;
v___y_4016_ = v_a_3969_;
v___y_4017_ = v_a_3970_;
goto v___jp_4013_;
}
else
{
if (v_noDefaults_3962_ == 0)
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v___f_3997_);
lean_dec_ref(v_use_3966_);
lean_dec(v_remove_3965_);
lean_dec(v_add_3964_);
v___x_4076_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4077_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4076_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
else
{
v___y_4014_ = v_a_3967_;
v___y_4015_ = v_a_3968_;
v___y_4016_ = v_a_3969_;
v___y_4017_ = v_a_3970_;
goto v___jp_4013_;
}
}
v___jp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___y_3973_);
lean_ctor_set(v___x_3975_, 1, v___y_3974_);
v___x_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
return v___x_3976_;
}
v___jp_3977_:
{
uint8_t v___x_3984_; 
v___x_3984_ = l_List_isEmpty___redArg(v_remove_3965_);
lean_dec(v_remove_3965_);
if (v___x_3984_ == 0)
{
if (v_noDefaults_3962_ == 0)
{
v___y_3973_ = v___y_3983_;
v___y_3974_ = v___y_3979_;
goto v___jp_3972_;
}
else
{
if (v_star_3963_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3979_);
v___x_3985_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3986_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3985_, v___y_3982_, v___y_3978_, v___y_3981_, v___y_3980_);
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
else
{
v___y_3973_ = v___y_3983_;
v___y_3974_ = v___y_3979_;
goto v___jp_3972_;
}
}
}
else
{
v___y_3973_ = v___y_3983_;
v___y_3974_ = v___y_3979_;
goto v___jp_3972_;
}
}
v___jp_3998_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_array_to_list(v___y_4005_);
lean_inc(v___y_4000_);
v___x_4007_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_4006_, v___y_4000_);
if (v_noDefaults_3962_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4008_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3964_, v___y_4000_);
v___x_4009_ = l_List_appendTR___redArg(v___x_4008_, v___x_4007_);
v___x_4010_ = l_List_appendTR___redArg(v___x_4009_, v___y_4004_);
v___y_3978_ = v___y_3999_;
v___y_3979_ = v___f_3997_;
v___y_3980_ = v___y_4002_;
v___y_3981_ = v___y_4001_;
v___y_3982_ = v___y_4003_;
v___y_3983_ = v___x_4010_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec(v___y_4004_);
v___x_4011_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3964_, v___y_4000_);
v___x_4012_ = l_List_appendTR___redArg(v___x_4011_, v___x_4007_);
v___y_3978_ = v___y_3999_;
v___y_3979_ = v___f_3997_;
v___y_3980_ = v___y_4002_;
v___y_3981_ = v___y_4001_;
v___y_3982_ = v___y_4003_;
v___y_3983_ = v___x_4012_;
goto v___jp_3977_;
}
}
v___jp_4013_:
{
lean_object* v_ref_4018_; lean_object* v_quotContext_4019_; lean_object* v_currMacroScope_4020_; lean_object* v___x_4021_; lean_object* v_a_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v_a_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v_a_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; size_t v_sz_4034_; size_t v___x_4035_; lean_object* v___x_4036_; 
v_ref_4018_ = lean_ctor_get(v___y_4016_, 5);
v_quotContext_4019_ = lean_ctor_get(v___y_4016_, 10);
v_currMacroScope_4020_ = lean_ctor_get(v___y_4016_, 11);
v___x_4021_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref(v___x_4021_);
v___x_4023_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4024_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_4020_, 2);
lean_inc_n(v_quotContext_4019_, 2);
v___x_4027_ = l_Lean_addMacroScope(v_quotContext_4019_, v___x_4026_, v_currMacroScope_4020_);
v___x_4028_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4029_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref(v___x_4029_);
v___x_4031_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4032_ = l_Lean_addMacroScope(v_quotContext_4019_, v___x_4031_, v_currMacroScope_4020_);
v___x_4033_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4034_ = lean_array_size(v_use_3966_);
v___x_4035_ = ((size_t)0ULL);
v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4034_, v___x_4035_, v_use_3966_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref(v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_4020_, 2);
lean_inc_n(v_quotContext_4019_, 2);
v___x_4039_ = l_Lean_addMacroScope(v_quotContext_4019_, v___x_4038_, v_currMacroScope_4020_);
v___x_4040_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4041_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4042_ = l_Lean_addMacroScope(v_quotContext_4019_, v___x_4041_, v_currMacroScope_4020_);
v___x_4043_ = 0;
v___x_4044_ = l_Lean_SourceInfo_fromRef(v_ref_4018_, v___x_4043_);
v___x_4045_ = lean_box(0);
v___x_4046_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4047_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4044_);
lean_ctor_set(v___x_4047_, 1, v___x_4023_);
lean_ctor_set(v___x_4047_, 2, v___x_4027_);
lean_ctor_set(v___x_4047_, 3, v___x_4046_);
v___x_4048_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4049_, 0, v_a_4022_);
lean_ctor_set(v___x_4049_, 1, v___x_4028_);
lean_ctor_set(v___x_4049_, 2, v___x_4032_);
lean_ctor_set(v___x_4049_, 3, v___x_4048_);
v___x_4050_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4051_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4051_, 0, v_a_4025_);
lean_ctor_set(v___x_4051_, 1, v___x_4033_);
lean_ctor_set(v___x_4051_, 2, v___x_4039_);
lean_ctor_set(v___x_4051_, 3, v___x_4050_);
v___x_4052_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4053_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4053_, 0, v_a_4030_);
lean_ctor_set(v___x_4053_, 1, v___x_4040_);
lean_ctor_set(v___x_4053_, 2, v___x_4042_);
lean_ctor_set(v___x_4053_, 3, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
lean_ctor_set(v___x_4054_, 1, v___x_4045_);
v___x_4055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4051_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4049_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4047_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4057_, v___x_4045_);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4061_ = lean_array_get_size(v_a_4037_);
v___x_4062_ = lean_nat_dec_lt(v___x_4059_, v___x_4061_);
if (v___x_4062_ == 0)
{
lean_dec(v_a_4037_);
v___y_3999_ = v___y_4015_;
v___y_4000_ = v___x_4045_;
v___y_4001_ = v___y_4016_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4014_;
v___y_4004_ = v___x_4058_;
v___y_4005_ = v___x_4060_;
goto v___jp_3998_;
}
else
{
uint8_t v___x_4063_; 
v___x_4063_ = lean_nat_dec_le(v___x_4061_, v___x_4061_);
if (v___x_4063_ == 0)
{
if (v___x_4062_ == 0)
{
lean_dec(v_a_4037_);
v___y_3999_ = v___y_4015_;
v___y_4000_ = v___x_4045_;
v___y_4001_ = v___y_4016_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4014_;
v___y_4004_ = v___x_4058_;
v___y_4005_ = v___x_4060_;
goto v___jp_3998_;
}
else
{
size_t v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_usize_of_nat(v___x_4061_);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4037_, v___x_4035_, v___x_4064_, v___x_4060_);
lean_dec(v_a_4037_);
v___y_3999_ = v___y_4015_;
v___y_4000_ = v___x_4045_;
v___y_4001_ = v___y_4016_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4014_;
v___y_4004_ = v___x_4058_;
v___y_4005_ = v___x_4065_;
goto v___jp_3998_;
}
}
else
{
size_t v___x_4066_; lean_object* v___x_4067_; 
v___x_4066_ = lean_usize_of_nat(v___x_4061_);
v___x_4067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4037_, v___x_4035_, v___x_4066_, v___x_4060_);
lean_dec(v_a_4037_);
v___y_3999_ = v___y_4015_;
v___y_4000_ = v___x_4045_;
v___y_4001_ = v___y_4016_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4014_;
v___y_4004_ = v___x_4058_;
v___y_4005_ = v___x_4067_;
goto v___jp_3998_;
}
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec(v___x_4032_);
lean_dec(v_a_4030_);
lean_dec(v___x_4027_);
lean_dec(v_a_4025_);
lean_dec(v_a_4022_);
lean_dec_ref(v___f_3997_);
lean_dec(v_remove_3965_);
lean_dec(v_add_3964_);
v_a_4068_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4036_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4036_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4086_, lean_object* v_star_4087_, lean_object* v_add_4088_, lean_object* v_remove_4089_, lean_object* v_use_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
uint8_t v_noDefaults_boxed_4096_; uint8_t v_star_boxed_4097_; lean_object* v_res_4098_; 
v_noDefaults_boxed_4096_ = lean_unbox(v_noDefaults_4086_);
v_star_boxed_4097_ = lean_unbox(v_star_4087_);
v_res_4098_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4096_, v_star_boxed_4097_, v_add_4088_, v_remove_4089_, v_use_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
lean_dec(v_a_4092_);
lean_dec_ref(v_a_4091_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4099_, size_t v_i_4100_, lean_object* v_bs_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4099_, v_i_4100_, v_bs_4101_, v___y_4104_, v___y_4105_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4108_, lean_object* v_i_4109_, lean_object* v_bs_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
size_t v_sz_boxed_4116_; size_t v_i_boxed_4117_; lean_object* v_res_4118_; 
v_sz_boxed_4116_ = lean_unbox_usize(v_sz_4108_);
lean_dec(v_sz_4108_);
v_i_boxed_4117_ = lean_unbox_usize(v_i_4109_);
lean_dec(v_i_4109_);
v_res_4118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4116_, v_i_boxed_4117_, v_bs_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4118_;
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
