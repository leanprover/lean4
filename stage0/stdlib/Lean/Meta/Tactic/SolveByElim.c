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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveByElim"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__2_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 179, 43, 63, 49, 24, 32, 221)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__5_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SolveByElim"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__6_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 128, 10, 73, 34, 87, 215, 23)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__8_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__9_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(220, 84, 21, 131, 251, 222, 234, 140)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__10_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__11_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 250, 155, 43, 152, 188, 125, 165)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__12_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__4_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 103, 71, 209, 42, 171, 248, 95)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__13_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__0_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 15, 125, 73, 29, 247, 113, 29)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__14_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__1_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 120, 191, 244, 248, 79, 174, 157)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__15_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__7_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 21, 26, 115, 214, 98, 174, 68)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__16_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1979843508) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(27, 195, 150, 22, 210, 98, 42, 14)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__17_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__18_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 174, 13, 231, 91, 76, 45, 40)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__19_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__20_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 50, 28, 209, 97, 190, 99, 237)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__21_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 173, 154, 40, 205, 78, 52, 57)}};
static const lean_object* l_Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_55_ = 0;
v___x_56_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__22_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_57_ = l_Lean_registerTraceClass(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
return v_res_59_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(32u);
v___x_61_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_63_ = ((size_t)5ULL);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_unsigned_to_nat(32u);
v___x_66_ = lean_mk_empty_array_with_capacity(v___x_65_);
v___x_67_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__0);
v___x_68_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
lean_ctor_set(v___x_68_, 2, v___x_64_);
lean_ctor_set(v___x_68_, 3, v___x_64_);
lean_ctor_set_usize(v___x_68_, 4, v___x_63_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_traceState_72_; lean_object* v_traces_73_; lean_object* v___x_74_; lean_object* v_traceState_75_; lean_object* v_env_76_; lean_object* v_nextMacroScope_77_; lean_object* v_ngen_78_; lean_object* v_auxDeclNGen_79_; lean_object* v_cache_80_; lean_object* v_messages_81_; lean_object* v_infoState_82_; lean_object* v_snapshotTasks_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_102_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_traceState_72_ = lean_ctor_get(v___x_71_, 4);
lean_inc_ref(v_traceState_72_);
lean_dec(v___x_71_);
v_traces_73_ = lean_ctor_get(v_traceState_72_, 0);
lean_inc_ref(v_traces_73_);
lean_dec_ref(v_traceState_72_);
v___x_74_ = lean_st_ref_take(v___y_69_);
v_traceState_75_ = lean_ctor_get(v___x_74_, 4);
v_env_76_ = lean_ctor_get(v___x_74_, 0);
v_nextMacroScope_77_ = lean_ctor_get(v___x_74_, 1);
v_ngen_78_ = lean_ctor_get(v___x_74_, 2);
v_auxDeclNGen_79_ = lean_ctor_get(v___x_74_, 3);
v_cache_80_ = lean_ctor_get(v___x_74_, 5);
v_messages_81_ = lean_ctor_get(v___x_74_, 6);
v_infoState_82_ = lean_ctor_get(v___x_74_, 7);
v_snapshotTasks_83_ = lean_ctor_get(v___x_74_, 8);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_102_ == 0)
{
v___x_85_ = v___x_74_;
v_isShared_86_ = v_isSharedCheck_102_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snapshotTasks_83_);
lean_inc(v_infoState_82_);
lean_inc(v_messages_81_);
lean_inc(v_cache_80_);
lean_inc(v_traceState_75_);
lean_inc(v_auxDeclNGen_79_);
lean_inc(v_ngen_78_);
lean_inc(v_nextMacroScope_77_);
lean_inc(v_env_76_);
lean_dec(v___x_74_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_102_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
uint64_t v_tid_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_100_; 
v_tid_87_ = lean_ctor_get_uint64(v_traceState_75_, sizeof(void*)*1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_traceState_75_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_traceState_75_, 0);
lean_dec(v_unused_101_);
v___x_89_ = v_traceState_75_;
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_traceState_75_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___closed__1);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_91_);
lean_ctor_set_uint64(v_reuseFailAlloc_99_, sizeof(void*)*1, v_tid_87_);
v___x_93_ = v_reuseFailAlloc_99_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 4, v___x_93_);
v___x_95_ = v___x_85_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_env_76_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_nextMacroScope_77_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_ngen_78_);
lean_ctor_set(v_reuseFailAlloc_98_, 3, v_auxDeclNGen_79_);
lean_ctor_set(v_reuseFailAlloc_98_, 4, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_98_, 5, v_cache_80_);
lean_ctor_set(v_reuseFailAlloc_98_, 6, v_messages_81_);
lean_ctor_set(v_reuseFailAlloc_98_, 7, v_infoState_82_);
lean_ctor_set(v_reuseFailAlloc_98_, 8, v_snapshotTasks_83_);
v___x_95_ = v_reuseFailAlloc_98_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_st_ref_set(v___y_69_, v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_traces_73_);
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg___boxed(lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_103_);
lean_dec(v___y_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
lean_object* v_name_120_; lean_object* v_defValue_121_; lean_object* v_map_122_; lean_object* v___x_123_; 
v_name_120_ = lean_ctor_get(v_opt_119_, 0);
v_defValue_121_ = lean_ctor_get(v_opt_119_, 1);
v_map_122_ = lean_ctor_get(v_opts_118_, 0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_122_, v_name_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_unbox(v_defValue_121_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; 
v_val_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v___x_123_);
if (lean_obj_tag(v_val_125_) == 1)
{
uint8_t v_v_126_; 
v_v_126_ = lean_ctor_get_uint8(v_val_125_, 0);
lean_dec_ref(v_val_125_);
return v_v_126_;
}
else
{
uint8_t v___x_127_; 
lean_dec(v_val_125_);
v___x_127_ = lean_unbox(v_defValue_121_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_128_, v_opt_129_);
lean_dec_ref(v_opt_129_);
lean_dec_ref(v_opts_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_saveState___redArg(v___y_134_, v___y_136_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
v___x_140_ = lean_apply_5(v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, lean_box(0));
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_a_139_);
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v_a_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_179_; 
v_a_150_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_179_ == 0)
{
v___x_152_ = v___x_140_;
v_isShared_153_ = v_isSharedCheck_179_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_140_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_179_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
uint8_t v___y_155_; uint8_t v___x_177_; 
v___x_177_ = l_Lean_Exception_isInterrupt(v_a_150_);
if (v___x_177_ == 0)
{
uint8_t v___x_178_; 
lean_inc(v_a_150_);
v___x_178_ = l_Lean_Exception_isRuntime(v_a_150_);
v___y_155_ = v___x_178_;
goto v___jp_154_;
}
else
{
v___y_155_ = v___x_177_;
goto v___jp_154_;
}
v___jp_154_:
{
if (v___y_155_ == 0)
{
lean_object* v___x_156_; 
lean_del_object(v___x_152_);
lean_dec(v_a_150_);
v___x_156_ = l_Lean_Meta_SavedState_restore___redArg(v_a_139_, v___y_134_, v___y_136_);
lean_dec(v_a_139_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v___x_156_, 0);
lean_dec(v_unused_165_);
v___x_158_ = v___x_156_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_dec(v___x_156_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_box(0);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_156_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_156_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v___x_175_; 
lean_dec(v_a_139_);
if (v_isShared_153_ == 0)
{
v___x_175_ = v___x_152_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_150_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v_x_132_);
v_a_180_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_138_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_138_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg___boxed(lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(lean_object* v_00_u03b1_195_, lean_object* v_x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v_00_u03b1_203_, lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v_00_u03b1_203_, v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_210_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_222_ = l_Lean_MessageData_ofExpr(v_e_214_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_225_, lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_225_, v_x_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec_ref(v_x_226_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(uint8_t v___x_233_, uint8_t v___x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v_x_236_);
return v___x_242_;
}
else
{
lean_object* v_head_243_; lean_object* v_tail_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_268_; 
v_head_243_ = lean_ctor_get(v_x_235_, 0);
v_tail_244_ = lean_ctor_get(v_x_235_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_268_ == 0)
{
v___x_246_ = v_x_235_;
v_isShared_247_ = v_isSharedCheck_268_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_tail_244_);
lean_inc(v_head_243_);
lean_dec(v_x_235_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_268_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v_a_249_; lean_object* v___x_255_; 
lean_inc(v_head_243_);
v___x_255_ = l_Lean_MVarId_inferInstance(v_head_243_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_dec_ref(v___x_255_);
v_a_249_ = v___x_233_;
goto v___jp_248_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_267_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_267_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_267_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint8_t v___y_261_; uint8_t v___x_265_; 
v___x_265_ = l_Lean_Exception_isInterrupt(v_a_256_);
if (v___x_265_ == 0)
{
uint8_t v___x_266_; 
lean_inc(v_a_256_);
v___x_266_ = l_Lean_Exception_isRuntime(v_a_256_);
v___y_261_ = v___x_266_;
goto v___jp_260_;
}
else
{
v___y_261_ = v___x_265_;
goto v___jp_260_;
}
v___jp_260_:
{
if (v___y_261_ == 0)
{
lean_del_object(v___x_258_);
lean_dec(v_a_256_);
v_a_249_ = v___x_234_;
goto v___jp_248_;
}
else
{
lean_object* v___x_263_; 
lean_del_object(v___x_246_);
lean_dec(v_tail_244_);
lean_dec(v_head_243_);
lean_dec(v_x_236_);
if (v_isShared_259_ == 0)
{
v___x_263_ = v___x_258_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_256_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
v___jp_248_:
{
if (v_a_249_ == 0)
{
lean_del_object(v___x_246_);
lean_dec(v_head_243_);
v_x_235_ = v_tail_244_;
goto _start;
}
else
{
lean_object* v___x_252_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_x_236_);
v___x_252_ = v___x_246_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_head_243_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_x_236_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v_x_235_ = v_tail_244_;
v_x_236_ = v___x_252_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v___x_14186__boxed_278_; uint8_t v___x_14187__boxed_279_; lean_object* v_res_280_; 
v___x_14186__boxed_278_ = lean_unbox(v___x_269_);
v___x_14187__boxed_279_ = lean_unbox(v___x_270_);
v_res_280_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_14186__boxed_278_, v___x_14187__boxed_279_, v_x_271_, v_x_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v_x_281_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 1);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v_x_281_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v_x_281_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 0);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg___boxed(lean_object* v_x_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_299_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(lean_object* v_e_302_){
_start:
{
if (lean_obj_tag(v_e_302_) == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 2;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2___boxed(lean_object* v_e_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_e_305_);
lean_dec_ref(v_e_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(lean_object* v_opts_308_, lean_object* v_opt_309_){
_start:
{
lean_object* v_name_310_; lean_object* v_defValue_311_; lean_object* v_map_312_; lean_object* v___x_313_; 
v_name_310_ = lean_ctor_get(v_opt_309_, 0);
v_defValue_311_ = lean_ctor_get(v_opt_309_, 1);
v_map_312_ = lean_ctor_get(v_opts_308_, 0);
v___x_313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_312_, v_name_310_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_inc(v_defValue_311_);
return v_defValue_311_;
}
else
{
lean_object* v_val_314_; 
v_val_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v_val_314_) == 3)
{
lean_object* v_v_315_; 
v_v_315_ = lean_ctor_get(v_val_314_, 0);
lean_inc(v_v_315_);
lean_dec_ref(v_val_314_);
return v_v_315_;
}
else
{
lean_dec(v_val_314_);
lean_inc(v_defValue_311_);
return v_defValue_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5___boxed(lean_object* v_opts_316_, lean_object* v_opt_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_316_, v_opt_317_);
lean_dec_ref(v_opt_317_);
lean_dec_ref(v_opts_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(size_t v_sz_319_, size_t v_i_320_, lean_object* v_bs_321_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = lean_usize_dec_lt(v_i_320_, v_sz_319_);
if (v___x_322_ == 0)
{
return v_bs_321_;
}
else
{
lean_object* v_v_323_; lean_object* v_msg_324_; lean_object* v___x_325_; lean_object* v_bs_x27_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v_v_323_ = lean_array_uget_borrowed(v_bs_321_, v_i_320_);
v_msg_324_ = lean_ctor_get(v_v_323_, 1);
lean_inc_ref(v_msg_324_);
v___x_325_ = lean_unsigned_to_nat(0u);
v_bs_x27_326_ = lean_array_uset(v_bs_321_, v_i_320_, v___x_325_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_i_320_, v___x_327_);
v___x_329_ = lean_array_uset(v_bs_x27_326_, v_i_320_, v_msg_324_);
v_i_320_ = v___x_328_;
v_bs_321_ = v___x_329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_331_, lean_object* v_i_332_, lean_object* v_bs_333_){
_start:
{
size_t v_sz_boxed_334_; size_t v_i_boxed_335_; lean_object* v_res_336_; 
v_sz_boxed_334_ = lean_unbox_usize(v_sz_331_);
lean_dec(v_sz_331_);
v_i_boxed_335_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_boxed_334_, v_i_boxed_335_, v_bs_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_env_344_; lean_object* v___x_345_; lean_object* v_mctx_346_; lean_object* v_lctx_347_; lean_object* v_options_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_343_ = lean_st_ref_get(v___y_341_);
v_env_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_env_344_);
lean_dec(v___x_343_);
v___x_345_ = lean_st_ref_get(v___y_339_);
v_mctx_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_mctx_346_);
lean_dec(v___x_345_);
v_lctx_347_ = lean_ctor_get(v___y_338_, 2);
v_options_348_ = lean_ctor_get(v___y_340_, 2);
lean_inc_ref(v_options_348_);
lean_inc_ref(v_lctx_347_);
v___x_349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_349_, 0, v_env_344_);
lean_ctor_set(v___x_349_, 1, v_mctx_346_);
lean_ctor_set(v___x_349_, 2, v_lctx_347_);
lean_ctor_set(v___x_349_, 3, v_options_348_);
v___x_350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_msgData_337_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6___boxed(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msgData_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(lean_object* v_oldTraces_359_, lean_object* v_data_360_, lean_object* v_ref_361_, lean_object* v_msg_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_fileName_368_; lean_object* v_fileMap_369_; lean_object* v_options_370_; lean_object* v_currRecDepth_371_; lean_object* v_maxRecDepth_372_; lean_object* v_ref_373_; lean_object* v_currNamespace_374_; lean_object* v_openDecls_375_; lean_object* v_initHeartbeats_376_; lean_object* v_maxHeartbeats_377_; lean_object* v_quotContext_378_; lean_object* v_currMacroScope_379_; uint8_t v_diag_380_; lean_object* v_cancelTk_x3f_381_; uint8_t v_suppressElabErrors_382_; lean_object* v_inheritedTraceOptions_383_; lean_object* v___x_384_; lean_object* v_traceState_385_; lean_object* v_traces_386_; lean_object* v_ref_387_; lean_object* v___x_388_; lean_object* v___x_389_; size_t v_sz_390_; size_t v___x_391_; lean_object* v___x_392_; lean_object* v_msg_393_; lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_432_; 
v_fileName_368_ = lean_ctor_get(v___y_365_, 0);
v_fileMap_369_ = lean_ctor_get(v___y_365_, 1);
v_options_370_ = lean_ctor_get(v___y_365_, 2);
v_currRecDepth_371_ = lean_ctor_get(v___y_365_, 3);
v_maxRecDepth_372_ = lean_ctor_get(v___y_365_, 4);
v_ref_373_ = lean_ctor_get(v___y_365_, 5);
v_currNamespace_374_ = lean_ctor_get(v___y_365_, 6);
v_openDecls_375_ = lean_ctor_get(v___y_365_, 7);
v_initHeartbeats_376_ = lean_ctor_get(v___y_365_, 8);
v_maxHeartbeats_377_ = lean_ctor_get(v___y_365_, 9);
v_quotContext_378_ = lean_ctor_get(v___y_365_, 10);
v_currMacroScope_379_ = lean_ctor_get(v___y_365_, 11);
v_diag_380_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*14);
v_cancelTk_x3f_381_ = lean_ctor_get(v___y_365_, 12);
v_suppressElabErrors_382_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_383_ = lean_ctor_get(v___y_365_, 13);
v___x_384_ = lean_st_ref_get(v___y_366_);
v_traceState_385_ = lean_ctor_get(v___x_384_, 4);
lean_inc_ref(v_traceState_385_);
lean_dec(v___x_384_);
v_traces_386_ = lean_ctor_get(v_traceState_385_, 0);
lean_inc_ref(v_traces_386_);
lean_dec_ref(v_traceState_385_);
v_ref_387_ = l_Lean_replaceRef(v_ref_361_, v_ref_373_);
lean_inc_ref(v_inheritedTraceOptions_383_);
lean_inc(v_cancelTk_x3f_381_);
lean_inc(v_currMacroScope_379_);
lean_inc(v_quotContext_378_);
lean_inc(v_maxHeartbeats_377_);
lean_inc(v_initHeartbeats_376_);
lean_inc(v_openDecls_375_);
lean_inc(v_currNamespace_374_);
lean_inc(v_maxRecDepth_372_);
lean_inc(v_currRecDepth_371_);
lean_inc_ref(v_options_370_);
lean_inc_ref(v_fileMap_369_);
lean_inc_ref(v_fileName_368_);
v___x_388_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_388_, 0, v_fileName_368_);
lean_ctor_set(v___x_388_, 1, v_fileMap_369_);
lean_ctor_set(v___x_388_, 2, v_options_370_);
lean_ctor_set(v___x_388_, 3, v_currRecDepth_371_);
lean_ctor_set(v___x_388_, 4, v_maxRecDepth_372_);
lean_ctor_set(v___x_388_, 5, v_ref_387_);
lean_ctor_set(v___x_388_, 6, v_currNamespace_374_);
lean_ctor_set(v___x_388_, 7, v_openDecls_375_);
lean_ctor_set(v___x_388_, 8, v_initHeartbeats_376_);
lean_ctor_set(v___x_388_, 9, v_maxHeartbeats_377_);
lean_ctor_set(v___x_388_, 10, v_quotContext_378_);
lean_ctor_set(v___x_388_, 11, v_currMacroScope_379_);
lean_ctor_set(v___x_388_, 12, v_cancelTk_x3f_381_);
lean_ctor_set(v___x_388_, 13, v_inheritedTraceOptions_383_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*14, v_diag_380_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*14 + 1, v_suppressElabErrors_382_);
v___x_389_ = l_Lean_PersistentArray_toArray___redArg(v_traces_386_);
lean_dec_ref(v_traces_386_);
v_sz_390_ = lean_array_size(v___x_389_);
v___x_391_ = ((size_t)0ULL);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__5(v_sz_390_, v___x_391_, v___x_389_);
v_msg_393_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_393_, 0, v_data_360_);
lean_ctor_set(v_msg_393_, 1, v_msg_362_);
lean_ctor_set(v_msg_393_, 2, v___x_392_);
v___x_394_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_393_, v___y_363_, v___y_364_, v___x_388_, v___y_366_);
lean_dec_ref(v___x_388_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_432_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_432_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_432_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v_traceState_400_; lean_object* v_env_401_; lean_object* v_nextMacroScope_402_; lean_object* v_ngen_403_; lean_object* v_auxDeclNGen_404_; lean_object* v_cache_405_; lean_object* v_messages_406_; lean_object* v_infoState_407_; lean_object* v_snapshotTasks_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_431_; 
v___x_399_ = lean_st_ref_take(v___y_366_);
v_traceState_400_ = lean_ctor_get(v___x_399_, 4);
v_env_401_ = lean_ctor_get(v___x_399_, 0);
v_nextMacroScope_402_ = lean_ctor_get(v___x_399_, 1);
v_ngen_403_ = lean_ctor_get(v___x_399_, 2);
v_auxDeclNGen_404_ = lean_ctor_get(v___x_399_, 3);
v_cache_405_ = lean_ctor_get(v___x_399_, 5);
v_messages_406_ = lean_ctor_get(v___x_399_, 6);
v_infoState_407_ = lean_ctor_get(v___x_399_, 7);
v_snapshotTasks_408_ = lean_ctor_get(v___x_399_, 8);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_431_ == 0)
{
v___x_410_ = v___x_399_;
v_isShared_411_ = v_isSharedCheck_431_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snapshotTasks_408_);
lean_inc(v_infoState_407_);
lean_inc(v_messages_406_);
lean_inc(v_cache_405_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_404_);
lean_inc(v_ngen_403_);
lean_inc(v_nextMacroScope_402_);
lean_inc(v_env_401_);
lean_dec(v___x_399_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_431_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint64_t v_tid_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_429_; 
v_tid_412_ = lean_ctor_get_uint64(v_traceState_400_, sizeof(void*)*1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_traceState_400_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_traceState_400_, 0);
lean_dec(v_unused_430_);
v___x_414_ = v_traceState_400_;
v_isShared_415_ = v_isSharedCheck_429_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_traceState_400_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_429_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_361_);
lean_ctor_set(v___x_416_, 1, v_a_395_);
v___x_417_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_359_, v___x_416_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_417_);
lean_ctor_set_uint64(v_reuseFailAlloc_428_, sizeof(void*)*1, v_tid_412_);
v___x_419_ = v_reuseFailAlloc_428_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 4, v___x_419_);
v___x_421_ = v___x_410_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_env_401_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_nextMacroScope_402_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_ngen_403_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_auxDeclNGen_404_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v_cache_405_);
lean_ctor_set(v_reuseFailAlloc_427_, 6, v_messages_406_);
lean_ctor_set(v_reuseFailAlloc_427_, 7, v_infoState_407_);
lean_ctor_set(v_reuseFailAlloc_427_, 8, v_snapshotTasks_408_);
v___x_421_ = v_reuseFailAlloc_427_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_422_ = lean_st_ref_set(v___y_366_, v___x_421_);
v___x_423_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_423_);
v___x_425_ = v___x_397_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3___boxed(lean_object* v_oldTraces_433_, lean_object* v_data_434_, lean_object* v_ref_435_, lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_433_, v_data_434_, v_ref_435_, v_msg_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__0));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2(void){
_start:
{
lean_object* v___x_446_; double v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_float_of_nat(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__3));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5(void){
_start:
{
lean_object* v___x_451_; double v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1000u);
v___x_452_ = lean_float_of_nat(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v_cls_453_, uint8_t v_collapsed_454_, lean_object* v_tag_455_, lean_object* v_opts_456_, uint8_t v_clsEnabled_457_, lean_object* v_oldTraces_458_, lean_object* v_msg_459_, lean_object* v_resStartStop_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_565_; 
v_fst_466_ = lean_ctor_get(v_resStartStop_460_, 0);
v_snd_467_ = lean_ctor_get(v_resStartStop_460_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_resStartStop_460_);
if (v_isSharedCheck_565_ == 0)
{
v___x_469_ = v_resStartStop_460_;
v_isShared_470_ = v_isSharedCheck_565_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v_resStartStop_460_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_565_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v_data_474_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_564_; 
v_fst_485_ = lean_ctor_get(v_snd_467_, 0);
v_snd_486_ = lean_ctor_get(v_snd_467_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_snd_467_);
if (v_isSharedCheck_564_ == 0)
{
v___x_488_ = v_snd_467_;
v_isShared_489_ = v_isSharedCheck_564_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_486_);
lean_inc(v_fst_485_);
lean_dec(v_snd_467_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_564_;
goto v_resetjp_487_;
}
v___jp_471_:
{
lean_object* v___x_475_; 
lean_inc(v___y_473_);
v___x_475_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3(v_oldTraces_458_, v_data_474_, v___y_473_, v___y_472_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; 
lean_dec_ref(v___x_475_);
v___x_476_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_466_);
return v___x_476_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_fst_466_);
v_a_477_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_475_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___y_493_; lean_object* v_a_494_; uint8_t v___y_518_; double v___y_549_; 
v___x_490_ = l_Lean_trace_profiler;
v___x_491_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_456_, v___x_490_);
if (v___x_491_ == 0)
{
v___y_518_ = v___x_491_;
goto v___jp_517_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = l_Lean_trace_profiler_useHeartbeats;
v___x_555_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_opts_456_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; double v___x_558_; double v___x_559_; double v___x_560_; 
v___x_556_ = l_Lean_trace_profiler_threshold;
v___x_557_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_456_, v___x_556_);
v___x_558_ = lean_float_of_nat(v___x_557_);
v___x_559_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__5);
v___x_560_ = lean_float_div(v___x_558_, v___x_559_);
v___y_549_ = v___x_560_;
goto v___jp_548_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; double v___x_563_; 
v___x_561_ = l_Lean_trace_profiler_threshold;
v___x_562_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__5(v_opts_456_, v___x_561_);
v___x_563_ = lean_float_of_nat(v___x_562_);
v___y_549_ = v___x_563_;
goto v___jp_548_;
}
}
v___jp_492_:
{
uint8_t v_result_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v_result_495_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__2(v_fst_466_);
v___x_496_ = l_Lean_TraceResult_toEmoji(v_result_495_);
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
v___x_498_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__1);
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 7);
lean_ctor_set(v___x_488_, 1, v___x_498_);
lean_ctor_set(v___x_488_, 0, v___x_497_);
v___x_500_ = v___x_488_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_511_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v_m_502_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set_tag(v___x_469_, 7);
lean_ctor_set(v___x_469_, 1, v_a_494_);
lean_ctor_set(v___x_469_, 0, v___x_500_);
v_m_502_ = v___x_469_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_a_494_);
v_m_502_ = v_reuseFailAlloc_510_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; double v___x_505_; lean_object* v_data_506_; 
v___x_503_ = lean_box(v_result_495_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__2);
lean_inc_ref(v_tag_455_);
lean_inc_ref(v___x_504_);
lean_inc(v_cls_453_);
v_data_506_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_506_, 0, v_cls_453_);
lean_ctor_set(v_data_506_, 1, v___x_504_);
lean_ctor_set(v_data_506_, 2, v_tag_455_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3, v___x_505_);
lean_ctor_set_float(v_data_506_, sizeof(void*)*3 + 8, v___x_505_);
lean_ctor_set_uint8(v_data_506_, sizeof(void*)*3 + 16, v_collapsed_454_);
if (v___x_491_ == 0)
{
lean_dec_ref(v___x_504_);
lean_dec(v_snd_486_);
lean_dec(v_fst_485_);
lean_dec_ref(v_tag_455_);
lean_dec(v_cls_453_);
v___y_472_ = v_m_502_;
v___y_473_ = v___y_493_;
v_data_474_ = v_data_506_;
goto v___jp_471_;
}
else
{
lean_object* v_data_507_; double v___x_508_; double v___x_509_; 
lean_dec_ref(v_data_506_);
v_data_507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_507_, 0, v_cls_453_);
lean_ctor_set(v_data_507_, 1, v___x_504_);
lean_ctor_set(v_data_507_, 2, v_tag_455_);
v___x_508_ = lean_unbox_float(v_fst_485_);
lean_dec(v_fst_485_);
lean_ctor_set_float(v_data_507_, sizeof(void*)*3, v___x_508_);
v___x_509_ = lean_unbox_float(v_snd_486_);
lean_dec(v_snd_486_);
lean_ctor_set_float(v_data_507_, sizeof(void*)*3 + 8, v___x_509_);
lean_ctor_set_uint8(v_data_507_, sizeof(void*)*3 + 16, v_collapsed_454_);
v___y_472_ = v_m_502_;
v___y_473_ = v___y_493_;
v_data_474_ = v_data_507_;
goto v___jp_471_;
}
}
}
}
v___jp_512_:
{
lean_object* v_ref_513_; lean_object* v___x_514_; 
v_ref_513_ = lean_ctor_get(v___y_463_, 5);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_461_);
lean_inc(v_fst_466_);
v___x_514_ = lean_apply_6(v_msg_459_, v_fst_466_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, lean_box(0));
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v___y_493_ = v_ref_513_;
v_a_494_ = v_a_515_;
goto v___jp_492_;
}
else
{
lean_object* v___x_516_; 
lean_dec_ref(v___x_514_);
v___x_516_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___closed__4);
v___y_493_ = v_ref_513_;
v_a_494_ = v___x_516_;
goto v___jp_492_;
}
}
v___jp_517_:
{
if (v_clsEnabled_457_ == 0)
{
if (v___y_518_ == 0)
{
lean_object* v___x_519_; lean_object* v_traceState_520_; lean_object* v_env_521_; lean_object* v_nextMacroScope_522_; lean_object* v_ngen_523_; lean_object* v_auxDeclNGen_524_; lean_object* v_cache_525_; lean_object* v_messages_526_; lean_object* v_infoState_527_; lean_object* v_snapshotTasks_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_547_; 
lean_del_object(v___x_488_);
lean_dec(v_snd_486_);
lean_dec(v_fst_485_);
lean_del_object(v___x_469_);
lean_dec_ref(v_msg_459_);
lean_dec_ref(v_tag_455_);
lean_dec(v_cls_453_);
v___x_519_ = lean_st_ref_take(v___y_464_);
v_traceState_520_ = lean_ctor_get(v___x_519_, 4);
v_env_521_ = lean_ctor_get(v___x_519_, 0);
v_nextMacroScope_522_ = lean_ctor_get(v___x_519_, 1);
v_ngen_523_ = lean_ctor_get(v___x_519_, 2);
v_auxDeclNGen_524_ = lean_ctor_get(v___x_519_, 3);
v_cache_525_ = lean_ctor_get(v___x_519_, 5);
v_messages_526_ = lean_ctor_get(v___x_519_, 6);
v_infoState_527_ = lean_ctor_get(v___x_519_, 7);
v_snapshotTasks_528_ = lean_ctor_get(v___x_519_, 8);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_547_ == 0)
{
v___x_530_ = v___x_519_;
v_isShared_531_ = v_isSharedCheck_547_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snapshotTasks_528_);
lean_inc(v_infoState_527_);
lean_inc(v_messages_526_);
lean_inc(v_cache_525_);
lean_inc(v_traceState_520_);
lean_inc(v_auxDeclNGen_524_);
lean_inc(v_ngen_523_);
lean_inc(v_nextMacroScope_522_);
lean_inc(v_env_521_);
lean_dec(v___x_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_547_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint64_t v_tid_532_; lean_object* v_traces_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_546_; 
v_tid_532_ = lean_ctor_get_uint64(v_traceState_520_, sizeof(void*)*1);
v_traces_533_ = lean_ctor_get(v_traceState_520_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_traceState_520_);
if (v_isSharedCheck_546_ == 0)
{
v___x_535_ = v_traceState_520_;
v_isShared_536_ = v_isSharedCheck_546_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_traces_533_);
lean_dec(v_traceState_520_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_546_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_458_, v_traces_533_);
lean_dec_ref(v_traces_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_537_);
lean_ctor_set_uint64(v_reuseFailAlloc_545_, sizeof(void*)*1, v_tid_532_);
v___x_539_ = v_reuseFailAlloc_545_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_541_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v___x_539_);
v___x_541_ = v___x_530_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_env_521_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_nextMacroScope_522_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_ngen_523_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_auxDeclNGen_524_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_544_, 5, v_cache_525_);
lean_ctor_set(v_reuseFailAlloc_544_, 6, v_messages_526_);
lean_ctor_set(v_reuseFailAlloc_544_, 7, v_infoState_527_);
lean_ctor_set(v_reuseFailAlloc_544_, 8, v_snapshotTasks_528_);
v___x_541_ = v_reuseFailAlloc_544_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_st_ref_set(v___y_464_, v___x_541_);
v___x_543_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_fst_466_);
return v___x_543_;
}
}
}
}
}
else
{
goto v___jp_512_;
}
}
else
{
goto v___jp_512_;
}
}
v___jp_548_:
{
double v___x_550_; double v___x_551_; double v___x_552_; uint8_t v___x_553_; 
v___x_550_ = lean_unbox_float(v_snd_486_);
v___x_551_ = lean_unbox_float(v_fst_485_);
v___x_552_ = lean_float_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_float_decLt(v___y_549_, v___x_552_);
v___y_518_ = v___x_553_;
goto v___jp_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v_cls_566_, lean_object* v_collapsed_567_, lean_object* v_tag_568_, lean_object* v_opts_569_, lean_object* v_clsEnabled_570_, lean_object* v_oldTraces_571_, lean_object* v_msg_572_, lean_object* v_resStartStop_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
uint8_t v_collapsed_boxed_579_; uint8_t v_clsEnabled_boxed_580_; lean_object* v_res_581_; 
v_collapsed_boxed_579_ = lean_unbox(v_collapsed_567_);
v_clsEnabled_boxed_580_ = lean_unbox(v_clsEnabled_570_);
v_res_581_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v_cls_566_, v_collapsed_boxed_579_, v_tag_568_, v_opts_569_, v_clsEnabled_boxed_580_, v_oldTraces_571_, v_msg_572_, v_resStartStop_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_opts_569_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(uint8_t v___x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
if (lean_obj_tag(v_x_583_) == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_x_584_);
return v___x_590_;
}
else
{
lean_object* v_head_591_; lean_object* v_tail_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_615_; 
v_head_591_ = lean_ctor_get(v_x_583_, 0);
v_tail_592_ = lean_ctor_get(v_x_583_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_615_ == 0)
{
v___x_594_ = v_x_583_;
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_tail_592_);
lean_inc(v_head_591_);
lean_dec(v_x_583_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; 
lean_inc(v_head_591_);
v___x_596_ = l_Lean_MVarId_inferInstance(v_head_591_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_dec_ref(v___x_596_);
lean_del_object(v___x_594_);
lean_dec(v_head_591_);
v_x_583_ = v_tail_592_;
goto _start;
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_614_; 
v_a_598_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_614_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_614_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_614_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___y_603_; uint8_t v___x_612_; 
v___x_612_ = l_Lean_Exception_isInterrupt(v_a_598_);
if (v___x_612_ == 0)
{
uint8_t v___x_613_; 
lean_inc(v_a_598_);
v___x_613_ = l_Lean_Exception_isRuntime(v_a_598_);
v___y_603_ = v___x_613_;
goto v___jp_602_;
}
else
{
v___y_603_ = v___x_612_;
goto v___jp_602_;
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
if (v___x_582_ == 0)
{
lean_del_object(v___x_594_);
lean_dec(v_head_591_);
v_x_583_ = v_tail_592_;
goto _start;
}
else
{
lean_object* v___x_606_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v_x_584_);
v___x_606_ = v___x_594_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_head_591_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_x_584_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_x_583_ = v_tail_592_;
v_x_584_ = v___x_606_;
goto _start;
}
}
}
else
{
lean_object* v___x_610_; 
lean_del_object(v___x_594_);
lean_dec(v_tail_592_);
lean_dec(v_head_591_);
lean_dec(v_x_584_);
if (v_isShared_601_ == 0)
{
v___x_610_ = v___x_600_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_598_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v___x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v___x_14652__boxed_624_; lean_object* v_res_625_; 
v___x_14652__boxed_624_ = lean_unbox(v___x_616_);
v_res_625_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_14652__boxed_624_, v_x_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_x_628_);
return v___x_634_;
}
else
{
lean_object* v_head_635_; lean_object* v_tail_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_659_; 
v_head_635_ = lean_ctor_get(v_x_627_, 0);
v_tail_636_ = lean_ctor_get(v_x_627_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_627_);
if (v_isSharedCheck_659_ == 0)
{
v___x_638_ = v_x_627_;
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_tail_636_);
lean_inc(v_head_635_);
lean_dec(v_x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_645_; 
lean_inc(v_head_635_);
v___x_645_ = l_Lean_MVarId_inferInstance(v_head_635_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref(v___x_645_);
if (v___x_626_ == 0)
{
lean_del_object(v___x_638_);
lean_dec(v_head_635_);
v_x_627_ = v_tail_636_;
goto _start;
}
else
{
goto v___jp_640_;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_658_; 
v_a_647_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_658_ == 0)
{
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_658_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
uint8_t v___y_652_; uint8_t v___x_656_; 
v___x_656_ = l_Lean_Exception_isInterrupt(v_a_647_);
if (v___x_656_ == 0)
{
uint8_t v___x_657_; 
lean_inc(v_a_647_);
v___x_657_ = l_Lean_Exception_isRuntime(v_a_647_);
v___y_652_ = v___x_657_;
goto v___jp_651_;
}
else
{
v___y_652_ = v___x_656_;
goto v___jp_651_;
}
v___jp_651_:
{
if (v___y_652_ == 0)
{
lean_del_object(v___x_649_);
lean_dec(v_a_647_);
goto v___jp_640_;
}
else
{
lean_object* v___x_654_; 
lean_del_object(v___x_638_);
lean_dec(v_tail_636_);
lean_dec(v_head_635_);
lean_dec(v_x_628_);
if (v_isShared_650_ == 0)
{
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_647_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
v___jp_640_:
{
lean_object* v___x_642_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v_x_628_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_head_635_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_x_628_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
v_x_627_ = v_tail_636_;
v_x_628_ = v___x_642_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_14729__boxed_668_; lean_object* v_res_669_; 
v___x_14729__boxed_668_ = lean_unbox(v___x_660_);
v_res_669_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14729__boxed_668_, v_x_661_, v_x_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_669_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_673_; double v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1000000000u);
v___x_674_ = lean_float_of_nat(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_675_, lean_object* v_g_676_, lean_object* v_e_677_, lean_object* v_cfg_678_, lean_object* v___x_679_, lean_object* v___x_680_, uint8_t v___x_681_, lean_object* v___x_682_, lean_object* v___f_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_options_689_; uint8_t v_hasTrace_690_; 
v_options_689_ = lean_ctor_get(v___y_686_, 2);
v_hasTrace_690_ = lean_ctor_get_uint8(v_options_689_, sizeof(void*)*1);
if (v_hasTrace_690_ == 0)
{
lean_object* v___x_691_; uint8_t v_foApprox_692_; uint8_t v_ctxApprox_693_; uint8_t v_quasiPatternApprox_694_; uint8_t v_constApprox_695_; uint8_t v_isDefEqStuckEx_696_; uint8_t v_unificationHints_697_; uint8_t v_proofIrrelevance_698_; uint8_t v_assignSyntheticOpaque_699_; uint8_t v_offsetCnstrs_700_; uint8_t v_etaStruct_701_; uint8_t v_univApprox_702_; uint8_t v_iota_703_; uint8_t v_beta_704_; uint8_t v_proj_705_; uint8_t v_zeta_706_; uint8_t v_zetaDelta_707_; uint8_t v_zetaUnused_708_; uint8_t v_zetaHave_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_680_);
v___x_691_ = l_Lean_Meta_Context_config(v___y_684_);
v_foApprox_692_ = lean_ctor_get_uint8(v___x_691_, 0);
v_ctxApprox_693_ = lean_ctor_get_uint8(v___x_691_, 1);
v_quasiPatternApprox_694_ = lean_ctor_get_uint8(v___x_691_, 2);
v_constApprox_695_ = lean_ctor_get_uint8(v___x_691_, 3);
v_isDefEqStuckEx_696_ = lean_ctor_get_uint8(v___x_691_, 4);
v_unificationHints_697_ = lean_ctor_get_uint8(v___x_691_, 5);
v_proofIrrelevance_698_ = lean_ctor_get_uint8(v___x_691_, 6);
v_assignSyntheticOpaque_699_ = lean_ctor_get_uint8(v___x_691_, 7);
v_offsetCnstrs_700_ = lean_ctor_get_uint8(v___x_691_, 8);
v_etaStruct_701_ = lean_ctor_get_uint8(v___x_691_, 10);
v_univApprox_702_ = lean_ctor_get_uint8(v___x_691_, 11);
v_iota_703_ = lean_ctor_get_uint8(v___x_691_, 12);
v_beta_704_ = lean_ctor_get_uint8(v___x_691_, 13);
v_proj_705_ = lean_ctor_get_uint8(v___x_691_, 14);
v_zeta_706_ = lean_ctor_get_uint8(v___x_691_, 15);
v_zetaDelta_707_ = lean_ctor_get_uint8(v___x_691_, 16);
v_zetaUnused_708_ = lean_ctor_get_uint8(v___x_691_, 17);
v_zetaHave_709_ = lean_ctor_get_uint8(v___x_691_, 18);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_747_ == 0)
{
v___x_711_ = v___x_691_;
v_isShared_712_ = v_isSharedCheck_747_;
goto v_resetjp_710_;
}
else
{
lean_dec(v___x_691_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_747_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v_trackZetaDelta_713_; lean_object* v_zetaDeltaSet_714_; lean_object* v_lctx_715_; lean_object* v_localInstances_716_; lean_object* v_defEqCtx_x3f_717_; lean_object* v_synthPendingDepth_718_; lean_object* v_canUnfold_x3f_719_; uint8_t v_univApprox_720_; uint8_t v_inTypeClassResolution_721_; uint8_t v_cacheInferType_722_; lean_object* v_config_724_; 
v_trackZetaDelta_713_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_714_ = lean_ctor_get(v___y_684_, 1);
v_lctx_715_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_716_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_717_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_718_ = lean_ctor_get(v___y_684_, 5);
v_canUnfold_x3f_719_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_720_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_721_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_722_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
if (v_isShared_712_ == 0)
{
v_config_724_ = v___x_711_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 0, v_foApprox_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 1, v_ctxApprox_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 2, v_quasiPatternApprox_694_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 3, v_constApprox_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 4, v_isDefEqStuckEx_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 5, v_unificationHints_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 6, v_proofIrrelevance_698_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 7, v_assignSyntheticOpaque_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 8, v_offsetCnstrs_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 10, v_etaStruct_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 11, v_univApprox_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 12, v_iota_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 13, v_beta_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 14, v_proj_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 15, v_zeta_706_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 16, v_zetaDelta_707_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 17, v_zetaUnused_708_);
lean_ctor_set_uint8(v_reuseFailAlloc_746_, 18, v_zetaHave_709_);
v_config_724_ = v_reuseFailAlloc_746_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v_key_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_ctor_set_uint8(v_config_724_, 9, v_transparency_675_);
v___x_725_ = l_Lean_Meta_Context_configKey(v___y_684_);
v___x_726_ = 2ULL;
v___x_727_ = lean_uint64_shift_right(v___x_725_, v___x_726_);
v___x_728_ = lean_uint64_shift_left(v___x_727_, v___x_726_);
v___x_729_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_675_);
v_key_730_ = lean_uint64_lor(v___x_728_, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_731_, 0, v_config_724_);
lean_ctor_set_uint64(v___x_731_, sizeof(void*)*1, v_key_730_);
lean_inc(v_canUnfold_x3f_719_);
lean_inc(v_synthPendingDepth_718_);
lean_inc(v_defEqCtx_x3f_717_);
lean_inc_ref(v_localInstances_716_);
lean_inc_ref(v_lctx_715_);
lean_inc(v_zetaDeltaSet_714_);
v___x_732_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_zetaDeltaSet_714_);
lean_ctor_set(v___x_732_, 2, v_lctx_715_);
lean_ctor_set(v___x_732_, 3, v_localInstances_716_);
lean_ctor_set(v___x_732_, 4, v_defEqCtx_x3f_717_);
lean_ctor_set(v___x_732_, 5, v_synthPendingDepth_718_);
lean_ctor_set(v___x_732_, 6, v_canUnfold_x3f_719_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*7, v_trackZetaDelta_713_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*7 + 1, v_univApprox_720_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*7 + 2, v_inTypeClassResolution_721_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*7 + 3, v_cacheInferType_722_);
v___x_733_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_732_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v_hasTrace_690_, v_a_734_, v___x_735_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = l_List_reverse___redArg(v_a_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
return v___x_736_;
}
}
else
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v_a_755_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v_a_770_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v_a_788_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v_a_800_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; 
v_inheritedTraceOptions_748_ = lean_ctor_get(v___y_686_, 13);
v___x_749_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
lean_inc(v___x_680_);
v___x_750_ = l_Lean_Name_append(v___x_749_, v___x_680_);
v___x_751_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_748_, v_options_689_, v___x_750_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = l_Lean_trace_profiler;
v___x_923_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_689_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; uint8_t v_foApprox_925_; uint8_t v_ctxApprox_926_; uint8_t v_quasiPatternApprox_927_; uint8_t v_constApprox_928_; uint8_t v_isDefEqStuckEx_929_; uint8_t v_unificationHints_930_; uint8_t v_proofIrrelevance_931_; uint8_t v_assignSyntheticOpaque_932_; uint8_t v_offsetCnstrs_933_; uint8_t v_etaStruct_934_; uint8_t v_univApprox_935_; uint8_t v_iota_936_; uint8_t v_beta_937_; uint8_t v_proj_938_; uint8_t v_zeta_939_; uint8_t v_zetaDelta_940_; uint8_t v_zetaUnused_941_; uint8_t v_zetaHave_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v___f_683_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_680_);
v___x_924_ = l_Lean_Meta_Context_config(v___y_684_);
v_foApprox_925_ = lean_ctor_get_uint8(v___x_924_, 0);
v_ctxApprox_926_ = lean_ctor_get_uint8(v___x_924_, 1);
v_quasiPatternApprox_927_ = lean_ctor_get_uint8(v___x_924_, 2);
v_constApprox_928_ = lean_ctor_get_uint8(v___x_924_, 3);
v_isDefEqStuckEx_929_ = lean_ctor_get_uint8(v___x_924_, 4);
v_unificationHints_930_ = lean_ctor_get_uint8(v___x_924_, 5);
v_proofIrrelevance_931_ = lean_ctor_get_uint8(v___x_924_, 6);
v_assignSyntheticOpaque_932_ = lean_ctor_get_uint8(v___x_924_, 7);
v_offsetCnstrs_933_ = lean_ctor_get_uint8(v___x_924_, 8);
v_etaStruct_934_ = lean_ctor_get_uint8(v___x_924_, 10);
v_univApprox_935_ = lean_ctor_get_uint8(v___x_924_, 11);
v_iota_936_ = lean_ctor_get_uint8(v___x_924_, 12);
v_beta_937_ = lean_ctor_get_uint8(v___x_924_, 13);
v_proj_938_ = lean_ctor_get_uint8(v___x_924_, 14);
v_zeta_939_ = lean_ctor_get_uint8(v___x_924_, 15);
v_zetaDelta_940_ = lean_ctor_get_uint8(v___x_924_, 16);
v_zetaUnused_941_ = lean_ctor_get_uint8(v___x_924_, 17);
v_zetaHave_942_ = lean_ctor_get_uint8(v___x_924_, 18);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_980_ == 0)
{
v___x_944_ = v___x_924_;
v_isShared_945_ = v_isSharedCheck_980_;
goto v_resetjp_943_;
}
else
{
lean_dec(v___x_924_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_980_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
uint8_t v_trackZetaDelta_946_; lean_object* v_zetaDeltaSet_947_; lean_object* v_lctx_948_; lean_object* v_localInstances_949_; lean_object* v_defEqCtx_x3f_950_; lean_object* v_synthPendingDepth_951_; lean_object* v_canUnfold_x3f_952_; uint8_t v_univApprox_953_; uint8_t v_inTypeClassResolution_954_; uint8_t v_cacheInferType_955_; lean_object* v_config_957_; 
v_trackZetaDelta_946_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_947_ = lean_ctor_get(v___y_684_, 1);
v_lctx_948_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_949_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_950_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_951_ = lean_ctor_get(v___y_684_, 5);
v_canUnfold_x3f_952_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_953_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_954_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_955_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
if (v_isShared_945_ == 0)
{
v_config_957_ = v___x_944_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 0, v_foApprox_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 1, v_ctxApprox_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 2, v_quasiPatternApprox_927_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 3, v_constApprox_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 4, v_isDefEqStuckEx_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 5, v_unificationHints_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 6, v_proofIrrelevance_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 7, v_assignSyntheticOpaque_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 8, v_offsetCnstrs_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 10, v_etaStruct_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 11, v_univApprox_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 12, v_iota_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 13, v_beta_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 14, v_proj_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 15, v_zeta_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 16, v_zetaDelta_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 17, v_zetaUnused_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, 18, v_zetaHave_942_);
v_config_957_ = v_reuseFailAlloc_979_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v___x_962_; uint64_t v_key_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_ctor_set_uint8(v_config_957_, 9, v_transparency_675_);
v___x_958_ = l_Lean_Meta_Context_configKey(v___y_684_);
v___x_959_ = 2ULL;
v___x_960_ = lean_uint64_shift_right(v___x_958_, v___x_959_);
v___x_961_ = lean_uint64_shift_left(v___x_960_, v___x_959_);
v___x_962_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_675_);
v_key_963_ = lean_uint64_lor(v___x_961_, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_964_, 0, v_config_957_);
lean_ctor_set_uint64(v___x_964_, sizeof(void*)*1, v_key_963_);
lean_inc(v_canUnfold_x3f_952_);
lean_inc(v_synthPendingDepth_951_);
lean_inc(v_defEqCtx_x3f_950_);
lean_inc_ref(v_localInstances_949_);
lean_inc_ref(v_lctx_948_);
lean_inc(v_zetaDeltaSet_947_);
v___x_965_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v_zetaDeltaSet_947_);
lean_ctor_set(v___x_965_, 2, v_lctx_948_);
lean_ctor_set(v___x_965_, 3, v_localInstances_949_);
lean_ctor_set(v___x_965_, 4, v_defEqCtx_x3f_950_);
lean_ctor_set(v___x_965_, 5, v_synthPendingDepth_951_);
lean_ctor_set(v___x_965_, 6, v_canUnfold_x3f_952_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*7, v_trackZetaDelta_946_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*7 + 1, v_univApprox_953_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*7 + 2, v_inTypeClassResolution_954_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*7 + 3, v_cacheInferType_955_);
v___x_966_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_965_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref(v___x_966_);
v___x_968_ = lean_box(0);
v___x_969_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_923_, v_hasTrace_690_, v_a_967_, v___x_968_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = l_List_reverse___redArg(v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
return v___x_969_;
}
}
else
{
return v___x_966_;
}
}
}
}
else
{
goto v___jp_815_;
}
}
else
{
goto v___jp_815_;
}
v___jp_752_:
{
lean_object* v___x_756_; double v___x_757_; double v___x_758_; double v___x_759_; double v___x_760_; double v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_756_ = lean_io_mono_nanos_now();
v___x_757_ = lean_float_of_nat(v___y_753_);
v___x_758_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_759_ = lean_float_div(v___x_757_, v___x_758_);
v___x_760_ = lean_float_of_nat(v___x_756_);
v___x_761_ = lean_float_div(v___x_760_, v___x_758_);
v___x_762_ = lean_box_float(v___x_759_);
v___x_763_ = lean_box_float(v___x_761_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_a_755_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_680_, v___x_681_, v___x_682_, v_options_689_, v___x_751_, v___y_754_, v___f_683_, v___x_765_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v_a_770_);
v___y_753_ = v___y_768_;
v___y_754_ = v___y_769_;
v_a_755_ = v___x_771_;
goto v___jp_752_;
}
v___jp_772_:
{
if (lean_obj_tag(v___y_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___y_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___y_775_);
v___y_768_ = v___y_773_;
v___y_769_ = v___y_774_;
v_a_770_ = v_a_776_;
goto v___jp_767_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_777_ = lean_ctor_get(v___y_775_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___y_775_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___y_775_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___y_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v___y_753_ = v___y_773_;
v___y_754_ = v___y_774_;
v_a_755_ = v___x_782_;
goto v___jp_752_;
}
}
}
}
v___jp_785_:
{
lean_object* v___x_789_; double v___x_790_; double v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_789_ = lean_io_get_num_heartbeats();
v___x_790_ = lean_float_of_nat(v___y_786_);
v___x_791_ = lean_float_of_nat(v___x_789_);
v___x_792_ = lean_box_float(v___x_790_);
v___x_793_ = lean_box_float(v___x_791_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_a_788_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_680_, v___x_681_, v___x_682_, v_options_689_, v___x_751_, v___y_787_, v___f_683_, v___x_795_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_796_;
}
v___jp_797_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v_a_800_);
v___y_786_ = v___y_798_;
v___y_787_ = v___y_799_;
v_a_788_ = v___x_801_;
goto v___jp_785_;
}
v___jp_802_:
{
if (lean_obj_tag(v___y_805_) == 0)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v___y_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___y_805_);
v___y_798_ = v___y_803_;
v___y_799_ = v___y_804_;
v_a_800_ = v_a_806_;
goto v___jp_797_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
v_a_807_ = lean_ctor_get(v___y_805_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___y_805_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___y_805_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___y_805_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 0);
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v___y_786_ = v___y_803_;
v___y_787_ = v___y_804_;
v_a_788_ = v___x_812_;
goto v___jp_785_;
}
}
}
}
v___jp_815_:
{
lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_816_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v___y_687_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v___x_818_ = l_Lean_trace_profiler_useHeartbeats;
v___x_819_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_689_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v_foApprox_822_; uint8_t v_ctxApprox_823_; uint8_t v_quasiPatternApprox_824_; uint8_t v_constApprox_825_; uint8_t v_isDefEqStuckEx_826_; uint8_t v_unificationHints_827_; uint8_t v_proofIrrelevance_828_; uint8_t v_assignSyntheticOpaque_829_; uint8_t v_offsetCnstrs_830_; uint8_t v_etaStruct_831_; uint8_t v_univApprox_832_; uint8_t v_iota_833_; uint8_t v_beta_834_; uint8_t v_proj_835_; uint8_t v_zeta_836_; uint8_t v_zetaDelta_837_; uint8_t v_zetaUnused_838_; uint8_t v_zetaHave_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_870_; 
v___x_820_ = lean_io_mono_nanos_now();
v___x_821_ = l_Lean_Meta_Context_config(v___y_684_);
v_foApprox_822_ = lean_ctor_get_uint8(v___x_821_, 0);
v_ctxApprox_823_ = lean_ctor_get_uint8(v___x_821_, 1);
v_quasiPatternApprox_824_ = lean_ctor_get_uint8(v___x_821_, 2);
v_constApprox_825_ = lean_ctor_get_uint8(v___x_821_, 3);
v_isDefEqStuckEx_826_ = lean_ctor_get_uint8(v___x_821_, 4);
v_unificationHints_827_ = lean_ctor_get_uint8(v___x_821_, 5);
v_proofIrrelevance_828_ = lean_ctor_get_uint8(v___x_821_, 6);
v_assignSyntheticOpaque_829_ = lean_ctor_get_uint8(v___x_821_, 7);
v_offsetCnstrs_830_ = lean_ctor_get_uint8(v___x_821_, 8);
v_etaStruct_831_ = lean_ctor_get_uint8(v___x_821_, 10);
v_univApprox_832_ = lean_ctor_get_uint8(v___x_821_, 11);
v_iota_833_ = lean_ctor_get_uint8(v___x_821_, 12);
v_beta_834_ = lean_ctor_get_uint8(v___x_821_, 13);
v_proj_835_ = lean_ctor_get_uint8(v___x_821_, 14);
v_zeta_836_ = lean_ctor_get_uint8(v___x_821_, 15);
v_zetaDelta_837_ = lean_ctor_get_uint8(v___x_821_, 16);
v_zetaUnused_838_ = lean_ctor_get_uint8(v___x_821_, 17);
v_zetaHave_839_ = lean_ctor_get_uint8(v___x_821_, 18);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_870_ == 0)
{
v___x_841_ = v___x_821_;
v_isShared_842_ = v_isSharedCheck_870_;
goto v_resetjp_840_;
}
else
{
lean_dec(v___x_821_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_870_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v_trackZetaDelta_843_; lean_object* v_zetaDeltaSet_844_; lean_object* v_lctx_845_; lean_object* v_localInstances_846_; lean_object* v_defEqCtx_x3f_847_; lean_object* v_synthPendingDepth_848_; lean_object* v_canUnfold_x3f_849_; uint8_t v_univApprox_850_; uint8_t v_inTypeClassResolution_851_; uint8_t v_cacheInferType_852_; lean_object* v_config_854_; 
v_trackZetaDelta_843_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_844_ = lean_ctor_get(v___y_684_, 1);
v_lctx_845_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_846_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_847_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_848_ = lean_ctor_get(v___y_684_, 5);
v_canUnfold_x3f_849_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_850_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_851_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_852_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
if (v_isShared_842_ == 0)
{
v_config_854_ = v___x_841_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 0, v_foApprox_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 1, v_ctxApprox_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 2, v_quasiPatternApprox_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 3, v_constApprox_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 4, v_isDefEqStuckEx_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 5, v_unificationHints_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 6, v_proofIrrelevance_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 7, v_assignSyntheticOpaque_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 8, v_offsetCnstrs_830_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 10, v_etaStruct_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 11, v_univApprox_832_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 12, v_iota_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 13, v_beta_834_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 14, v_proj_835_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 15, v_zeta_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 16, v_zetaDelta_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 17, v_zetaUnused_838_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, 18, v_zetaHave_839_);
v_config_854_ = v_reuseFailAlloc_869_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v_key_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_ctor_set_uint8(v_config_854_, 9, v_transparency_675_);
v___x_855_ = l_Lean_Meta_Context_configKey(v___y_684_);
v___x_856_ = 2ULL;
v___x_857_ = lean_uint64_shift_right(v___x_855_, v___x_856_);
v___x_858_ = lean_uint64_shift_left(v___x_857_, v___x_856_);
v___x_859_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_675_);
v_key_860_ = lean_uint64_lor(v___x_858_, v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_861_, 0, v_config_854_);
lean_ctor_set_uint64(v___x_861_, sizeof(void*)*1, v_key_860_);
lean_inc(v_canUnfold_x3f_849_);
lean_inc(v_synthPendingDepth_848_);
lean_inc(v_defEqCtx_x3f_847_);
lean_inc_ref(v_localInstances_846_);
lean_inc_ref(v_lctx_845_);
lean_inc(v_zetaDeltaSet_844_);
v___x_862_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_zetaDeltaSet_844_);
lean_ctor_set(v___x_862_, 2, v_lctx_845_);
lean_ctor_set(v___x_862_, 3, v_localInstances_846_);
lean_ctor_set(v___x_862_, 4, v_defEqCtx_x3f_847_);
lean_ctor_set(v___x_862_, 5, v_synthPendingDepth_848_);
lean_ctor_set(v___x_862_, 6, v_canUnfold_x3f_849_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*7, v_trackZetaDelta_843_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*7 + 1, v_univApprox_850_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*7 + 2, v_inTypeClassResolution_851_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*7 + 3, v_cacheInferType_852_);
v___x_863_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_862_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
v___x_865_ = lean_box(0);
v___x_866_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___x_819_, v_hasTrace_690_, v_a_864_, v___x_865_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = l_List_reverse___redArg(v_a_867_);
v___y_768_ = v___x_820_;
v___y_769_ = v_a_817_;
v_a_770_ = v___x_868_;
goto v___jp_767_;
}
else
{
v___y_773_ = v___x_820_;
v___y_774_ = v_a_817_;
v___y_775_ = v___x_866_;
goto v___jp_772_;
}
}
else
{
v___y_773_ = v___x_820_;
v___y_774_ = v_a_817_;
v___y_775_ = v___x_863_;
goto v___jp_772_;
}
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v_foApprox_873_; uint8_t v_ctxApprox_874_; uint8_t v_quasiPatternApprox_875_; uint8_t v_constApprox_876_; uint8_t v_isDefEqStuckEx_877_; uint8_t v_unificationHints_878_; uint8_t v_proofIrrelevance_879_; uint8_t v_assignSyntheticOpaque_880_; uint8_t v_offsetCnstrs_881_; uint8_t v_etaStruct_882_; uint8_t v_univApprox_883_; uint8_t v_iota_884_; uint8_t v_beta_885_; uint8_t v_proj_886_; uint8_t v_zeta_887_; uint8_t v_zetaDelta_888_; uint8_t v_zetaUnused_889_; uint8_t v_zetaHave_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_921_; 
v___x_871_ = lean_io_get_num_heartbeats();
v___x_872_ = l_Lean_Meta_Context_config(v___y_684_);
v_foApprox_873_ = lean_ctor_get_uint8(v___x_872_, 0);
v_ctxApprox_874_ = lean_ctor_get_uint8(v___x_872_, 1);
v_quasiPatternApprox_875_ = lean_ctor_get_uint8(v___x_872_, 2);
v_constApprox_876_ = lean_ctor_get_uint8(v___x_872_, 3);
v_isDefEqStuckEx_877_ = lean_ctor_get_uint8(v___x_872_, 4);
v_unificationHints_878_ = lean_ctor_get_uint8(v___x_872_, 5);
v_proofIrrelevance_879_ = lean_ctor_get_uint8(v___x_872_, 6);
v_assignSyntheticOpaque_880_ = lean_ctor_get_uint8(v___x_872_, 7);
v_offsetCnstrs_881_ = lean_ctor_get_uint8(v___x_872_, 8);
v_etaStruct_882_ = lean_ctor_get_uint8(v___x_872_, 10);
v_univApprox_883_ = lean_ctor_get_uint8(v___x_872_, 11);
v_iota_884_ = lean_ctor_get_uint8(v___x_872_, 12);
v_beta_885_ = lean_ctor_get_uint8(v___x_872_, 13);
v_proj_886_ = lean_ctor_get_uint8(v___x_872_, 14);
v_zeta_887_ = lean_ctor_get_uint8(v___x_872_, 15);
v_zetaDelta_888_ = lean_ctor_get_uint8(v___x_872_, 16);
v_zetaUnused_889_ = lean_ctor_get_uint8(v___x_872_, 17);
v_zetaHave_890_ = lean_ctor_get_uint8(v___x_872_, 18);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_921_ == 0)
{
v___x_892_ = v___x_872_;
v_isShared_893_ = v_isSharedCheck_921_;
goto v_resetjp_891_;
}
else
{
lean_dec(v___x_872_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_921_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
uint8_t v_trackZetaDelta_894_; lean_object* v_zetaDeltaSet_895_; lean_object* v_lctx_896_; lean_object* v_localInstances_897_; lean_object* v_defEqCtx_x3f_898_; lean_object* v_synthPendingDepth_899_; lean_object* v_canUnfold_x3f_900_; uint8_t v_univApprox_901_; uint8_t v_inTypeClassResolution_902_; uint8_t v_cacheInferType_903_; lean_object* v_config_905_; 
v_trackZetaDelta_894_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7);
v_zetaDeltaSet_895_ = lean_ctor_get(v___y_684_, 1);
v_lctx_896_ = lean_ctor_get(v___y_684_, 2);
v_localInstances_897_ = lean_ctor_get(v___y_684_, 3);
v_defEqCtx_x3f_898_ = lean_ctor_get(v___y_684_, 4);
v_synthPendingDepth_899_ = lean_ctor_get(v___y_684_, 5);
v_canUnfold_x3f_900_ = lean_ctor_get(v___y_684_, 6);
v_univApprox_901_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_902_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 2);
v_cacheInferType_903_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*7 + 3);
if (v_isShared_893_ == 0)
{
v_config_905_ = v___x_892_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 0, v_foApprox_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 1, v_ctxApprox_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 2, v_quasiPatternApprox_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 3, v_constApprox_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 4, v_isDefEqStuckEx_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 5, v_unificationHints_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 6, v_proofIrrelevance_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 7, v_assignSyntheticOpaque_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 8, v_offsetCnstrs_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 10, v_etaStruct_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 11, v_univApprox_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 12, v_iota_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 13, v_beta_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 14, v_proj_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 15, v_zeta_887_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 16, v_zetaDelta_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 17, v_zetaUnused_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, 18, v_zetaHave_890_);
v_config_905_ = v_reuseFailAlloc_920_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v_key_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_ctor_set_uint8(v_config_905_, 9, v_transparency_675_);
v___x_906_ = l_Lean_Meta_Context_configKey(v___y_684_);
v___x_907_ = 2ULL;
v___x_908_ = lean_uint64_shift_right(v___x_906_, v___x_907_);
v___x_909_ = lean_uint64_shift_left(v___x_908_, v___x_907_);
v___x_910_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_675_);
v_key_911_ = lean_uint64_lor(v___x_909_, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_912_, 0, v_config_905_);
lean_ctor_set_uint64(v___x_912_, sizeof(void*)*1, v_key_911_);
lean_inc(v_canUnfold_x3f_900_);
lean_inc(v_synthPendingDepth_899_);
lean_inc(v_defEqCtx_x3f_898_);
lean_inc_ref(v_localInstances_897_);
lean_inc_ref(v_lctx_896_);
lean_inc(v_zetaDeltaSet_895_);
v___x_913_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v_zetaDeltaSet_895_);
lean_ctor_set(v___x_913_, 2, v_lctx_896_);
lean_ctor_set(v___x_913_, 3, v_localInstances_897_);
lean_ctor_set(v___x_913_, 4, v_defEqCtx_x3f_898_);
lean_ctor_set(v___x_913_, 5, v_synthPendingDepth_899_);
lean_ctor_set(v___x_913_, 6, v_canUnfold_x3f_900_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*7, v_trackZetaDelta_894_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*7 + 1, v_univApprox_901_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*7 + 2, v_inTypeClassResolution_902_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*7 + 3, v_cacheInferType_903_);
v___x_914_ = l_Lean_MVarId_apply(v_g_676_, v_e_677_, v_cfg_678_, v___x_679_, v___x_913_, v___y_685_, v___y_686_, v___y_687_);
lean_dec_ref(v___x_913_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = lean_box(0);
v___x_917_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_819_, v_a_915_, v___x_916_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref(v___x_917_);
v___x_919_ = l_List_reverse___redArg(v_a_918_);
v___y_798_ = v___x_871_;
v___y_799_ = v_a_817_;
v_a_800_ = v___x_919_;
goto v___jp_797_;
}
else
{
v___y_803_ = v___x_871_;
v___y_804_ = v_a_817_;
v___y_805_ = v___x_917_;
goto v___jp_802_;
}
}
else
{
v___y_803_ = v___x_871_;
v___y_804_ = v_a_817_;
v___y_805_ = v___x_914_;
goto v___jp_802_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_981_, lean_object* v_g_982_, lean_object* v_e_983_, lean_object* v_cfg_984_, lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v___f_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_transparency_boxed_995_; uint8_t v___x_14817__boxed_996_; lean_object* v_res_997_; 
v_transparency_boxed_995_ = lean_unbox(v_transparency_981_);
v___x_14817__boxed_996_ = lean_unbox(v___x_987_);
v_res_997_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_995_, v_g_982_, v_e_983_, v_cfg_984_, v___x_985_, v___x_986_, v___x_14817__boxed_996_, v___x_988_, v___f_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_999_, lean_object* v_g_1000_, lean_object* v_cfg_1001_, lean_object* v_e_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; 
lean_inc_ref(v_e_1002_);
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1008_, 0, v_e_1002_);
v___x_1009_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1010_ = lean_box(0);
v___x_1011_ = 1;
v___x_1012_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1013_ = lean_box(v_transparency_999_);
v___x_1014_ = lean_box(v___x_1011_);
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1015_, 0, v___x_1013_);
lean_closure_set(v___f_1015_, 1, v_g_1000_);
lean_closure_set(v___f_1015_, 2, v_e_1002_);
lean_closure_set(v___f_1015_, 3, v_cfg_1001_);
lean_closure_set(v___f_1015_, 4, v___x_1010_);
lean_closure_set(v___f_1015_, 5, v___x_1009_);
lean_closure_set(v___f_1015_, 6, v___x_1014_);
lean_closure_set(v___f_1015_, 7, v___x_1012_);
lean_closure_set(v___f_1015_, 8, v___f_1008_);
v___x_1016_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___f_1015_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1017_, lean_object* v_g_1018_, lean_object* v_cfg_1019_, lean_object* v_e_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
uint8_t v_transparency_boxed_1026_; lean_object* v_res_1027_; 
v_transparency_boxed_1026_ = lean_unbox(v_transparency_1017_);
v_res_1027_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1026_, v_g_1018_, v_cfg_1019_, v_e_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1028_, uint8_t v_transparency_1029_, lean_object* v_lemmas_1030_, lean_object* v_g_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1030_, v_a_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1046_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1046_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_box(v_transparency_1029_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1041_, 0, v___x_1040_);
lean_closure_set(v___f_1041_, 1, v_g_1031_);
lean_closure_set(v___f_1041_, 2, v_cfg_1028_);
v___x_1042_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1042_, 0, lean_box(0));
lean_closure_set(v___x_1042_, 1, lean_box(0));
lean_closure_set(v___x_1042_, 2, v___f_1041_);
lean_closure_set(v___x_1042_, 3, v_a_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1042_);
v___x_1044_ = v___x_1038_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_g_1031_);
lean_dec_ref(v_cfg_1028_);
v_a_1047_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1035_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1035_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1055_, lean_object* v_transparency_1056_, lean_object* v_lemmas_1057_, lean_object* v_g_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
uint8_t v_transparency_boxed_1062_; lean_object* v_res_1063_; 
v_transparency_boxed_1062_ = lean_unbox(v_transparency_1056_);
v_res_1063_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1055_, v_transparency_boxed_1062_, v_lemmas_1057_, v_g_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec(v_a_1059_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1064_, uint8_t v_transparency_1065_, lean_object* v_lemmas_1066_, lean_object* v_g_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1064_, v_transparency_1065_, v_lemmas_1066_, v_g_1067_, v_a_1069_, v_a_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1074_, lean_object* v_transparency_1075_, lean_object* v_lemmas_1076_, lean_object* v_g_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
uint8_t v_transparency_boxed_1083_; lean_object* v_res_1084_; 
v_transparency_boxed_1083_ = lean_unbox(v_transparency_1075_);
v_res_1084_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1074_, v_transparency_boxed_1083_, v_lemmas_1076_, v_g_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(lean_object* v_00_u03b1_1085_, lean_object* v_x_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___redArg(v_x_1086_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__4(v_00_u03b1_1093_, v_x_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1101_, uint8_t v_transparency_1102_, lean_object* v_lemmas_1103_, lean_object* v_g_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1101_, v_transparency_1102_, v_lemmas_1103_, v_g_1104_, v_a_1106_, v_a_1108_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = l_Lean_Meta_Iterator_head___redArg(v_a_1111_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1112_;
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1110_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1110_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1121_, lean_object* v_transparency_1122_, lean_object* v_lemmas_1123_, lean_object* v_g_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
uint8_t v_transparency_boxed_1130_; lean_object* v_res_1131_; 
v_transparency_boxed_1130_ = lean_unbox(v_transparency_1122_);
v_res_1131_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1121_, v_transparency_boxed_1130_, v_lemmas_1123_, v_g_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1132_){
_start:
{
lean_object* v_toApplyRulesConfig_1133_; lean_object* v_toBacktrackConfig_1134_; 
v_toApplyRulesConfig_1133_ = lean_ctor_get(v_x_1132_, 0);
v_toBacktrackConfig_1134_ = lean_ctor_get(v_toApplyRulesConfig_1133_, 0);
lean_inc_ref(v_toBacktrackConfig_1134_);
return v_toBacktrackConfig_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1135_);
lean_dec_ref(v_x_1135_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1139_, lean_object* v_discharge_1140_, lean_object* v_g_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
lean_inc(v___y_1145_);
lean_inc_ref(v___y_1144_);
lean_inc(v___y_1143_);
lean_inc_ref(v___y_1142_);
lean_inc(v_g_1141_);
v___x_1147_ = lean_apply_6(v_test_1139_, v_g_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, lean_box(0));
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1158_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1158_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v___x_1152_; 
v___x_1152_ = lean_unbox(v_a_1148_);
lean_dec(v_a_1148_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_del_object(v___x_1150_);
lean_inc(v___y_1145_);
lean_inc_ref(v___y_1144_);
lean_inc(v___y_1143_);
lean_inc_ref(v___y_1142_);
v___x_1153_ = lean_apply_6(v_discharge_1140_, v_g_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, lean_box(0));
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
lean_dec(v_g_1141_);
lean_dec_ref(v_discharge_1140_);
v___x_1154_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1154_);
v___x_1156_ = v___x_1150_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
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
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_g_1141_);
lean_dec_ref(v_discharge_1140_);
v_a_1159_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1147_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1147_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1167_, lean_object* v_discharge_1168_, lean_object* v_g_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1167_, v_discharge_1168_, v_g_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1176_, lean_object* v_test_1177_){
_start:
{
lean_object* v_toApplyRulesConfig_1178_; lean_object* v_toBacktrackConfig_1179_; uint8_t v_backtracking_1180_; uint8_t v_intro_1181_; uint8_t v_constructor_1182_; uint8_t v_suggestions_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1215_; 
v_toApplyRulesConfig_1178_ = lean_ctor_get(v_cfg_1176_, 0);
lean_inc_ref(v_toApplyRulesConfig_1178_);
v_toBacktrackConfig_1179_ = lean_ctor_get(v_toApplyRulesConfig_1178_, 0);
lean_inc_ref(v_toBacktrackConfig_1179_);
v_backtracking_1180_ = lean_ctor_get_uint8(v_cfg_1176_, sizeof(void*)*1);
v_intro_1181_ = lean_ctor_get_uint8(v_cfg_1176_, sizeof(void*)*1 + 1);
v_constructor_1182_ = lean_ctor_get_uint8(v_cfg_1176_, sizeof(void*)*1 + 2);
v_suggestions_1183_ = lean_ctor_get_uint8(v_cfg_1176_, sizeof(void*)*1 + 3);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_cfg_1176_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_cfg_1176_, 0);
lean_dec(v_unused_1216_);
v___x_1185_ = v_cfg_1176_;
v_isShared_1186_ = v_isSharedCheck_1215_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v_cfg_1176_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1215_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_toApplyConfig_1187_; uint8_t v_transparency_1188_; uint8_t v_symm_1189_; uint8_t v_exfalso_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1213_; 
v_toApplyConfig_1187_ = lean_ctor_get(v_toApplyRulesConfig_1178_, 1);
v_transparency_1188_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1178_, sizeof(void*)*2);
v_symm_1189_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1178_, sizeof(void*)*2 + 1);
v_exfalso_1190_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1178_, sizeof(void*)*2 + 2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_toApplyRulesConfig_1178_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_toApplyRulesConfig_1178_, 0);
lean_dec(v_unused_1214_);
v___x_1192_ = v_toApplyRulesConfig_1178_;
v_isShared_1193_ = v_isSharedCheck_1213_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_toApplyConfig_1187_);
lean_dec(v_toApplyRulesConfig_1178_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1213_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_maxDepth_1194_; lean_object* v_proc_1195_; lean_object* v_suspend_1196_; lean_object* v_discharge_1197_; uint8_t v_commitIndependentGoals_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1212_; 
v_maxDepth_1194_ = lean_ctor_get(v_toBacktrackConfig_1179_, 0);
v_proc_1195_ = lean_ctor_get(v_toBacktrackConfig_1179_, 1);
v_suspend_1196_ = lean_ctor_get(v_toBacktrackConfig_1179_, 2);
v_discharge_1197_ = lean_ctor_get(v_toBacktrackConfig_1179_, 3);
v_commitIndependentGoals_1198_ = lean_ctor_get_uint8(v_toBacktrackConfig_1179_, sizeof(void*)*4);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_toBacktrackConfig_1179_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1200_ = v_toBacktrackConfig_1179_;
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_discharge_1197_);
lean_inc(v_suspend_1196_);
lean_inc(v_proc_1195_);
lean_inc(v_maxDepth_1194_);
lean_dec(v_toBacktrackConfig_1179_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1212_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___f_1202_; lean_object* v___x_1204_; 
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1202_, 0, v_test_1177_);
lean_closure_set(v___f_1202_, 1, v_discharge_1197_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 3, v___f_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_maxDepth_1194_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_proc_1195_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_suspend_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v___f_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*4, v_commitIndependentGoals_1198_);
v___x_1204_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1204_);
v___x_1206_ = v___x_1192_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_toApplyConfig_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*2, v_transparency_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*2 + 1, v_symm_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1210_, sizeof(void*)*2 + 2, v_exfalso_1190_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1206_);
v___x_1208_ = v___x_1185_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*1, v_backtracking_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*1 + 1, v_intro_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*1 + 2, v_constructor_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1209_, sizeof(void*)*1 + 3, v_suggestions_1183_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1217_, lean_object* v_proc_1218_, lean_object* v_orig_1219_, lean_object* v_goals_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
if (lean_obj_tag(v_goals_1220_) == 0)
{
lean_object* v___x_1226_; 
lean_dec_ref(v_proc_1218_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
v___x_1226_ = lean_apply_7(v_proc_1217_, v_orig_1219_, v_goals_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
return v___x_1226_;
}
else
{
lean_object* v_head_1227_; lean_object* v_tail_1228_; lean_object* v___x_1229_; 
v_head_1227_ = lean_ctor_get(v_goals_1220_, 0);
v_tail_1228_ = lean_ctor_get(v_goals_1220_, 1);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v_head_1227_);
v___x_1229_ = lean_apply_6(v_proc_1218_, v_head_1227_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1239_; 
lean_inc(v_tail_1228_);
lean_dec_ref(v_goals_1220_);
lean_dec(v_orig_1219_);
lean_dec_ref(v_proc_1217_);
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1239_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1239_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1234_ = l_List_appendTR___redArg(v_a_1230_, v_tail_1228_);
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1235_);
v___x_1237_ = v___x_1232_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1252_; 
v_a_1240_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1242_ = v___x_1229_;
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1229_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v___y_1245_; uint8_t v___x_1250_; 
v___x_1250_ = l_Lean_Exception_isInterrupt(v_a_1240_);
if (v___x_1250_ == 0)
{
uint8_t v___x_1251_; 
lean_inc(v_a_1240_);
v___x_1251_ = l_Lean_Exception_isRuntime(v_a_1240_);
v___y_1245_ = v___x_1251_;
goto v___jp_1244_;
}
else
{
v___y_1245_ = v___x_1250_;
goto v___jp_1244_;
}
v___jp_1244_:
{
if (v___y_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_del_object(v___x_1242_);
lean_dec(v_a_1240_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
v___x_1246_ = lean_apply_7(v_proc_1217_, v_orig_1219_, v_goals_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
return v___x_1246_;
}
else
{
lean_object* v___x_1248_; 
lean_dec_ref(v_goals_1220_);
lean_dec(v_orig_1219_);
lean_dec_ref(v_proc_1217_);
if (v_isShared_1243_ == 0)
{
v___x_1248_ = v___x_1242_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1240_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1253_, lean_object* v_proc_1254_, lean_object* v_orig_1255_, lean_object* v_goals_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1253_, v_proc_1254_, v_orig_1255_, v_goals_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1263_, lean_object* v_proc_1264_){
_start:
{
lean_object* v_toApplyRulesConfig_1265_; lean_object* v_toBacktrackConfig_1266_; uint8_t v_backtracking_1267_; uint8_t v_intro_1268_; uint8_t v_constructor_1269_; uint8_t v_suggestions_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1302_; 
v_toApplyRulesConfig_1265_ = lean_ctor_get(v_cfg_1263_, 0);
lean_inc_ref(v_toApplyRulesConfig_1265_);
v_toBacktrackConfig_1266_ = lean_ctor_get(v_toApplyRulesConfig_1265_, 0);
lean_inc_ref(v_toBacktrackConfig_1266_);
v_backtracking_1267_ = lean_ctor_get_uint8(v_cfg_1263_, sizeof(void*)*1);
v_intro_1268_ = lean_ctor_get_uint8(v_cfg_1263_, sizeof(void*)*1 + 1);
v_constructor_1269_ = lean_ctor_get_uint8(v_cfg_1263_, sizeof(void*)*1 + 2);
v_suggestions_1270_ = lean_ctor_get_uint8(v_cfg_1263_, sizeof(void*)*1 + 3);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_cfg_1263_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_cfg_1263_, 0);
lean_dec(v_unused_1303_);
v___x_1272_ = v_cfg_1263_;
v_isShared_1273_ = v_isSharedCheck_1302_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_cfg_1263_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1302_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v_toApplyConfig_1274_; uint8_t v_transparency_1275_; uint8_t v_symm_1276_; uint8_t v_exfalso_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1300_; 
v_toApplyConfig_1274_ = lean_ctor_get(v_toApplyRulesConfig_1265_, 1);
v_transparency_1275_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1265_, sizeof(void*)*2);
v_symm_1276_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1265_, sizeof(void*)*2 + 1);
v_exfalso_1277_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1265_, sizeof(void*)*2 + 2);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_toApplyRulesConfig_1265_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_toApplyRulesConfig_1265_, 0);
lean_dec(v_unused_1301_);
v___x_1279_ = v_toApplyRulesConfig_1265_;
v_isShared_1280_ = v_isSharedCheck_1300_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_toApplyConfig_1274_);
lean_dec(v_toApplyRulesConfig_1265_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1300_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_maxDepth_1281_; lean_object* v_proc_1282_; lean_object* v_suspend_1283_; lean_object* v_discharge_1284_; uint8_t v_commitIndependentGoals_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1299_; 
v_maxDepth_1281_ = lean_ctor_get(v_toBacktrackConfig_1266_, 0);
v_proc_1282_ = lean_ctor_get(v_toBacktrackConfig_1266_, 1);
v_suspend_1283_ = lean_ctor_get(v_toBacktrackConfig_1266_, 2);
v_discharge_1284_ = lean_ctor_get(v_toBacktrackConfig_1266_, 3);
v_commitIndependentGoals_1285_ = lean_ctor_get_uint8(v_toBacktrackConfig_1266_, sizeof(void*)*4);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_toBacktrackConfig_1266_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1287_ = v_toBacktrackConfig_1266_;
v_isShared_1288_ = v_isSharedCheck_1299_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_discharge_1284_);
lean_inc(v_suspend_1283_);
lean_inc(v_proc_1282_);
lean_inc(v_maxDepth_1281_);
lean_dec(v_toBacktrackConfig_1266_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1299_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___f_1289_; lean_object* v___x_1291_; 
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1289_, 0, v_proc_1282_);
lean_closure_set(v___f_1289_, 1, v_proc_1264_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___f_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_maxDepth_1281_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___f_1289_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_suspend_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_discharge_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1298_, sizeof(void*)*4, v_commitIndependentGoals_1285_);
v___x_1291_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1291_);
v___x_1293_ = v___x_1279_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_toApplyConfig_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*2, v_transparency_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*2 + 1, v_symm_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*2 + 2, v_exfalso_1277_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1293_);
v___x_1295_ = v___x_1272_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*1, v_backtracking_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*1 + 1, v_intro_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*1 + 2, v_constructor_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*1 + 3, v_suggestions_1270_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = 1;
v___x_1311_ = l_Lean_Meta_intro1Core(v_g_1304_, v___x_1310_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1329_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1329_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1329_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_snd_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1327_; 
v_snd_1316_ = lean_ctor_get(v_a_1312_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_a_1312_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_a_1312_, 0);
lean_dec(v_unused_1328_);
v___x_1318_ = v_a_1312_;
v_isShared_1319_ = v_isSharedCheck_1327_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_snd_1316_);
lean_dec(v_a_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1327_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(0);
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
lean_ctor_set(v___x_1318_, 1, v___x_1320_);
lean_ctor_set(v___x_1318_, 0, v_snd_1316_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_snd_1316_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1322_);
v___x_1324_ = v___x_1314_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
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
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1311_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1311_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1346_){
_start:
{
lean_object* v___f_1347_; lean_object* v___x_1348_; 
v___f_1347_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1348_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1346_, v___f_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_ks_1353_; lean_object* v_vs_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1378_; 
v_ks_1353_ = lean_ctor_get(v_x_1349_, 0);
v_vs_1354_ = lean_ctor_get(v_x_1349_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1349_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1356_ = v_x_1349_;
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_vs_1354_);
lean_inc(v_ks_1353_);
lean_dec(v_x_1349_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1378_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = lean_array_get_size(v_ks_1353_);
v___x_1359_ = lean_nat_dec_lt(v_x_1350_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
lean_dec(v_x_1350_);
v___x_1360_ = lean_array_push(v_ks_1353_, v_x_1351_);
v___x_1361_ = lean_array_push(v_vs_1354_, v_x_1352_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1361_);
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1363_ = v___x_1356_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
lean_object* v_k_x27_1365_; uint8_t v___x_1366_; 
v_k_x27_1365_ = lean_array_fget_borrowed(v_ks_1353_, v_x_1350_);
v___x_1366_ = l_Lean_instBEqMVarId_beq(v_x_1351_, v_k_x27_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1368_; 
if (v_isShared_1357_ == 0)
{
v___x_1368_ = v___x_1356_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_ks_1353_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_vs_1354_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_x_1350_, v___x_1369_);
lean_dec(v_x_1350_);
v_x_1349_ = v___x_1368_;
v_x_1350_ = v___x_1370_;
goto _start;
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1373_ = lean_array_fset(v_ks_1353_, v_x_1350_, v_x_1351_);
v___x_1374_ = lean_array_fset(v_vs_1354_, v_x_1350_, v_x_1352_);
lean_dec(v_x_1350_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1374_);
lean_ctor_set(v___x_1356_, 0, v___x_1373_);
v___x_1376_ = v___x_1356_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1379_, lean_object* v_k_1380_, lean_object* v_v_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1379_, v___x_1382_, v_k_1380_, v_v_1381_);
return v___x_1383_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; 
v___x_1384_ = ((size_t)5ULL);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_shift_left(v___x_1385_, v___x_1384_);
return v___x_1386_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; 
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1389_ = lean_usize_sub(v___x_1388_, v___x_1387_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1391_, size_t v_x_1392_, size_t v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1391_) == 0)
{
lean_object* v_es_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v_j_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_es_1396_ = lean_ctor_get(v_x_1391_, 0);
v___x_1397_ = ((size_t)5ULL);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1400_ = lean_usize_land(v_x_1392_, v___x_1399_);
v_j_1401_ = lean_usize_to_nat(v___x_1400_);
v___x_1402_ = lean_array_get_size(v_es_1396_);
v___x_1403_ = lean_nat_dec_lt(v_j_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_dec(v_j_1401_);
lean_dec(v_x_1395_);
lean_dec(v_x_1394_);
return v_x_1391_;
}
else
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1440_; 
lean_inc_ref(v_es_1396_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_x_1391_, 0);
lean_dec(v_unused_1441_);
v___x_1405_ = v_x_1391_;
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v_x_1391_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1440_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_v_1407_; lean_object* v___x_1408_; lean_object* v_xs_x27_1409_; lean_object* v___y_1411_; 
v_v_1407_ = lean_array_fget(v_es_1396_, v_j_1401_);
v___x_1408_ = lean_box(0);
v_xs_x27_1409_ = lean_array_fset(v_es_1396_, v_j_1401_, v___x_1408_);
switch(lean_obj_tag(v_v_1407_))
{
case 0:
{
lean_object* v_key_1416_; lean_object* v_val_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1427_; 
v_key_1416_ = lean_ctor_get(v_v_1407_, 0);
v_val_1417_ = lean_ctor_get(v_v_1407_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1419_ = v_v_1407_;
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_val_1417_);
lean_inc(v_key_1416_);
lean_dec(v_v_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1427_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___x_1421_; 
v___x_1421_ = l_Lean_instBEqMVarId_beq(v_x_1394_, v_key_1416_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1419_);
v___x_1422_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1416_, v_val_1417_, v_x_1394_, v_x_1395_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___y_1411_ = v___x_1423_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_val_1417_);
lean_dec(v_key_1416_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_x_1395_);
lean_ctor_set(v___x_1419_, 0, v_x_1394_);
v___x_1425_ = v___x_1419_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_x_1394_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_x_1395_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v___y_1411_ = v___x_1425_;
goto v___jp_1410_;
}
}
}
}
case 1:
{
lean_object* v_node_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1438_; 
v_node_1428_ = lean_ctor_get(v_v_1407_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_v_1407_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1430_ = v_v_1407_;
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_node_1428_);
lean_dec(v_v_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1438_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1432_ = lean_usize_shift_right(v_x_1392_, v___x_1397_);
v___x_1433_ = lean_usize_add(v_x_1393_, v___x_1398_);
v___x_1434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1428_, v___x_1432_, v___x_1433_, v_x_1394_, v_x_1395_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1434_);
v___x_1436_ = v___x_1430_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v___y_1411_ = v___x_1436_;
goto v___jp_1410_;
}
}
}
default: 
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_x_1394_);
lean_ctor_set(v___x_1439_, 1, v_x_1395_);
v___y_1411_ = v___x_1439_;
goto v___jp_1410_;
}
}
v___jp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_array_fset(v_xs_x27_1409_, v_j_1401_, v___y_1411_);
lean_dec(v_j_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1412_);
v___x_1414_ = v___x_1405_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_ks_1442_; lean_object* v_vs_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1463_; 
v_ks_1442_ = lean_ctor_get(v_x_1391_, 0);
v_vs_1443_ = lean_ctor_get(v_x_1391_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1391_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1445_ = v_x_1391_;
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_vs_1443_);
lean_inc(v_ks_1442_);
lean_dec(v_x_1391_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1463_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_ks_1442_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_vs_1443_);
v___x_1448_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v_newNode_1449_; uint8_t v___y_1451_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_newNode_1449_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1448_, v_x_1394_, v_x_1395_);
v___x_1457_ = ((size_t)7ULL);
v___x_1458_ = lean_usize_dec_le(v___x_1457_, v_x_1393_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v___x_1459_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1449_);
v___x_1460_ = lean_unsigned_to_nat(4u);
v___x_1461_ = lean_nat_dec_lt(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
v___y_1451_ = v___x_1461_;
goto v___jp_1450_;
}
else
{
v___y_1451_ = v___x_1458_;
goto v___jp_1450_;
}
v___jp_1450_:
{
if (v___y_1451_ == 0)
{
lean_object* v_ks_1452_; lean_object* v_vs_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_ks_1452_ = lean_ctor_get(v_newNode_1449_, 0);
lean_inc_ref(v_ks_1452_);
v_vs_1453_ = lean_ctor_get(v_newNode_1449_, 1);
lean_inc_ref(v_vs_1453_);
lean_dec_ref(v_newNode_1449_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1393_, v_ks_1452_, v_vs_1453_, v___x_1454_, v___x_1455_);
lean_dec_ref(v_vs_1453_);
lean_dec_ref(v_ks_1452_);
return v___x_1456_;
}
else
{
return v_newNode_1449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = lean_array_get_size(v_keys_1465_);
v___x_1470_ = lean_nat_dec_lt(v_i_1467_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v_i_1467_);
return v_entries_1468_;
}
else
{
lean_object* v_k_1471_; lean_object* v_v_1472_; uint64_t v___x_1473_; size_t v_h_1474_; size_t v___x_1475_; lean_object* v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v_h_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_k_1471_ = lean_array_fget_borrowed(v_keys_1465_, v_i_1467_);
v_v_1472_ = lean_array_fget_borrowed(v_vals_1466_, v_i_1467_);
v___x_1473_ = l_Lean_instHashableMVarId_hash(v_k_1471_);
v_h_1474_ = lean_uint64_to_usize(v___x_1473_);
v___x_1475_ = ((size_t)5ULL);
v___x_1476_ = lean_unsigned_to_nat(1u);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_sub(v_depth_1464_, v___x_1477_);
v___x_1479_ = lean_usize_mul(v___x_1475_, v___x_1478_);
v_h_1480_ = lean_usize_shift_right(v_h_1474_, v___x_1479_);
v___x_1481_ = lean_nat_add(v_i_1467_, v___x_1476_);
lean_dec(v_i_1467_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
v___x_1482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1468_, v_h_1480_, v_depth_1464_, v_k_1471_, v_v_1472_);
v_i_1467_ = v___x_1481_;
v_entries_1468_ = v___x_1482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1484_, lean_object* v_keys_1485_, lean_object* v_vals_1486_, lean_object* v_i_1487_, lean_object* v_entries_1488_){
_start:
{
size_t v_depth_boxed_1489_; lean_object* v_res_1490_; 
v_depth_boxed_1489_ = lean_unbox_usize(v_depth_1484_);
lean_dec(v_depth_1484_);
v_res_1490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1489_, v_keys_1485_, v_vals_1486_, v_i_1487_, v_entries_1488_);
lean_dec_ref(v_vals_1486_);
lean_dec_ref(v_keys_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_){
_start:
{
size_t v_x_834__boxed_1496_; size_t v_x_835__boxed_1497_; lean_object* v_res_1498_; 
v_x_834__boxed_1496_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_x_835__boxed_1497_ = lean_unbox_usize(v_x_1493_);
lean_dec(v_x_1493_);
v_res_1498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1491_, v_x_834__boxed_1496_, v_x_835__boxed_1497_, v_x_1494_, v_x_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
uint64_t v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1502_ = l_Lean_instHashableMVarId_hash(v_x_1500_);
v___x_1503_ = lean_uint64_to_usize(v___x_1502_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1499_, v___x_1503_, v___x_1504_, v_x_1500_, v_x_1501_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1506_, lean_object* v_val_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_mctx_1511_; lean_object* v_cache_1512_; lean_object* v_zetaDeltaFVarIds_1513_; lean_object* v_postponed_1514_; lean_object* v_diag_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1542_; 
v___x_1510_ = lean_st_ref_take(v___y_1508_);
v_mctx_1511_ = lean_ctor_get(v___x_1510_, 0);
v_cache_1512_ = lean_ctor_get(v___x_1510_, 1);
v_zetaDeltaFVarIds_1513_ = lean_ctor_get(v___x_1510_, 2);
v_postponed_1514_ = lean_ctor_get(v___x_1510_, 3);
v_diag_1515_ = lean_ctor_get(v___x_1510_, 4);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1517_ = v___x_1510_;
v_isShared_1518_ = v_isSharedCheck_1542_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_diag_1515_);
lean_inc(v_postponed_1514_);
lean_inc(v_zetaDeltaFVarIds_1513_);
lean_inc(v_cache_1512_);
lean_inc(v_mctx_1511_);
lean_dec(v___x_1510_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1542_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_depth_1519_; lean_object* v_levelAssignDepth_1520_; lean_object* v_mvarCounter_1521_; lean_object* v_lDepth_1522_; lean_object* v_decls_1523_; lean_object* v_userNames_1524_; lean_object* v_lAssignment_1525_; lean_object* v_eAssignment_1526_; lean_object* v_dAssignment_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1541_; 
v_depth_1519_ = lean_ctor_get(v_mctx_1511_, 0);
v_levelAssignDepth_1520_ = lean_ctor_get(v_mctx_1511_, 1);
v_mvarCounter_1521_ = lean_ctor_get(v_mctx_1511_, 2);
v_lDepth_1522_ = lean_ctor_get(v_mctx_1511_, 3);
v_decls_1523_ = lean_ctor_get(v_mctx_1511_, 4);
v_userNames_1524_ = lean_ctor_get(v_mctx_1511_, 5);
v_lAssignment_1525_ = lean_ctor_get(v_mctx_1511_, 6);
v_eAssignment_1526_ = lean_ctor_get(v_mctx_1511_, 7);
v_dAssignment_1527_ = lean_ctor_get(v_mctx_1511_, 8);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_mctx_1511_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1529_ = v_mctx_1511_;
v_isShared_1530_ = v_isSharedCheck_1541_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_dAssignment_1527_);
lean_inc(v_eAssignment_1526_);
lean_inc(v_lAssignment_1525_);
lean_inc(v_userNames_1524_);
lean_inc(v_decls_1523_);
lean_inc(v_lDepth_1522_);
lean_inc(v_mvarCounter_1521_);
lean_inc(v_levelAssignDepth_1520_);
lean_inc(v_depth_1519_);
lean_dec(v_mctx_1511_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1541_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1526_, v_mvarId_1506_, v_val_1507_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 7, v___x_1531_);
v___x_1533_ = v___x_1529_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_depth_1519_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_levelAssignDepth_1520_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_mvarCounter_1521_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_lDepth_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_decls_1523_);
lean_ctor_set(v_reuseFailAlloc_1540_, 5, v_userNames_1524_);
lean_ctor_set(v_reuseFailAlloc_1540_, 6, v_lAssignment_1525_);
lean_ctor_set(v_reuseFailAlloc_1540_, 7, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1540_, 8, v_dAssignment_1527_);
v___x_1533_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1533_);
v___x_1535_ = v___x_1517_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_cache_1512_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_zetaDeltaFVarIds_1513_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_postponed_1514_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_diag_1515_);
v___x_1535_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_st_ref_set(v___y_1508_, v___x_1535_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1543_, lean_object* v_val_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1543_, v_val_1544_, v___y_1545_);
lean_dec(v___y_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
lean_inc(v_g_1548_);
v___x_1554_ = l_Lean_MVarId_getType(v_g_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = lean_box(0);
v___x_1557_ = l_Lean_Meta_synthInstance(v_a_1555_, v___x_1556_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1548_, v_a_1558_, v___y_1550_);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v___x_1559_, 0);
lean_dec(v_unused_1568_);
v___x_1561_ = v___x_1559_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v___x_1559_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_box(0);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_g_1548_);
v_a_1569_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1557_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1557_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_g_1548_);
v_a_1577_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1554_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1554_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1593_){
_start:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; 
v___f_1594_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1595_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1593_, v___f_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1596_, lean_object* v_val_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1596_, v_val_1597_, v___y_1599_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1604_, lean_object* v_val_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1604_, v_val_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1613_, v_x_1614_, v_x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1617_, lean_object* v_x_1618_, size_t v_x_1619_, size_t v_x_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1618_, v_x_1619_, v_x_1620_, v_x_1621_, v_x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
size_t v_x_1165__boxed_1630_; size_t v_x_1166__boxed_1631_; lean_object* v_res_1632_; 
v_x_1165__boxed_1630_ = lean_unbox_usize(v_x_1626_);
lean_dec(v_x_1626_);
v_x_1166__boxed_1631_ = lean_unbox_usize(v_x_1627_);
lean_dec(v_x_1627_);
v_res_1632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1624_, v_x_1625_, v_x_1165__boxed_1630_, v_x_1166__boxed_1631_, v_x_1628_, v_x_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1633_, lean_object* v_n_1634_, lean_object* v_k_1635_, lean_object* v_v_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1634_, v_k_1635_, v_v_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1638_, size_t v_depth_1639_, lean_object* v_keys_1640_, lean_object* v_vals_1641_, lean_object* v_heq_1642_, lean_object* v_i_1643_, lean_object* v_entries_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1639_, v_keys_1640_, v_vals_1641_, v_i_1643_, v_entries_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1646_, lean_object* v_depth_1647_, lean_object* v_keys_1648_, lean_object* v_vals_1649_, lean_object* v_heq_1650_, lean_object* v_i_1651_, lean_object* v_entries_1652_){
_start:
{
size_t v_depth_boxed_1653_; lean_object* v_res_1654_; 
v_depth_boxed_1653_ = lean_unbox_usize(v_depth_1647_);
lean_dec(v_depth_1647_);
v_res_1654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1646_, v_depth_boxed_1653_, v_keys_1648_, v_vals_1649_, v_heq_1650_, v_i_1651_, v_entries_1652_);
lean_dec_ref(v_vals_1649_);
lean_dec_ref(v_keys_1648_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1656_, v_x_1657_, v_x_1658_, v_x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1661_, lean_object* v_discharge_1662_, lean_object* v_g_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v_g_1663_);
v___x_1669_ = lean_apply_6(v_discharge_1661_, v_g_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, lean_box(0));
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_dec(v_g_1663_);
lean_dec_ref(v_discharge_1662_);
return v___x_1669_;
}
else
{
lean_object* v_a_1670_; uint8_t v___y_1672_; uint8_t v___x_1674_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
v___x_1674_ = l_Lean_Exception_isInterrupt(v_a_1670_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = l_Lean_Exception_isRuntime(v_a_1670_);
v___y_1672_ = v___x_1675_;
goto v___jp_1671_;
}
else
{
lean_dec(v_a_1670_);
v___y_1672_ = v___x_1674_;
goto v___jp_1671_;
}
v___jp_1671_:
{
if (v___y_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_dec_ref(v___x_1669_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
v___x_1673_ = lean_apply_6(v_discharge_1662_, v_g_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, lean_box(0));
return v___x_1673_;
}
else
{
lean_dec(v_g_1663_);
lean_dec_ref(v_discharge_1662_);
return v___x_1669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1676_, lean_object* v_discharge_1677_, lean_object* v_g_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1676_, v_discharge_1677_, v_g_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1685_, lean_object* v_discharge_1686_){
_start:
{
lean_object* v_toApplyRulesConfig_1687_; lean_object* v_toBacktrackConfig_1688_; uint8_t v_backtracking_1689_; uint8_t v_intro_1690_; uint8_t v_constructor_1691_; uint8_t v_suggestions_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1724_; 
v_toApplyRulesConfig_1687_ = lean_ctor_get(v_cfg_1685_, 0);
lean_inc_ref(v_toApplyRulesConfig_1687_);
v_toBacktrackConfig_1688_ = lean_ctor_get(v_toApplyRulesConfig_1687_, 0);
lean_inc_ref(v_toBacktrackConfig_1688_);
v_backtracking_1689_ = lean_ctor_get_uint8(v_cfg_1685_, sizeof(void*)*1);
v_intro_1690_ = lean_ctor_get_uint8(v_cfg_1685_, sizeof(void*)*1 + 1);
v_constructor_1691_ = lean_ctor_get_uint8(v_cfg_1685_, sizeof(void*)*1 + 2);
v_suggestions_1692_ = lean_ctor_get_uint8(v_cfg_1685_, sizeof(void*)*1 + 3);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_cfg_1685_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_cfg_1685_, 0);
lean_dec(v_unused_1725_);
v___x_1694_ = v_cfg_1685_;
v_isShared_1695_ = v_isSharedCheck_1724_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v_cfg_1685_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1724_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_toApplyConfig_1696_; uint8_t v_transparency_1697_; uint8_t v_symm_1698_; uint8_t v_exfalso_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1722_; 
v_toApplyConfig_1696_ = lean_ctor_get(v_toApplyRulesConfig_1687_, 1);
v_transparency_1697_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1687_, sizeof(void*)*2);
v_symm_1698_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1687_, sizeof(void*)*2 + 1);
v_exfalso_1699_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1687_, sizeof(void*)*2 + 2);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_toApplyRulesConfig_1687_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v_toApplyRulesConfig_1687_, 0);
lean_dec(v_unused_1723_);
v___x_1701_ = v_toApplyRulesConfig_1687_;
v_isShared_1702_ = v_isSharedCheck_1722_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_toApplyConfig_1696_);
lean_dec(v_toApplyRulesConfig_1687_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1722_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_maxDepth_1703_; lean_object* v_proc_1704_; lean_object* v_suspend_1705_; lean_object* v_discharge_1706_; uint8_t v_commitIndependentGoals_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1721_; 
v_maxDepth_1703_ = lean_ctor_get(v_toBacktrackConfig_1688_, 0);
v_proc_1704_ = lean_ctor_get(v_toBacktrackConfig_1688_, 1);
v_suspend_1705_ = lean_ctor_get(v_toBacktrackConfig_1688_, 2);
v_discharge_1706_ = lean_ctor_get(v_toBacktrackConfig_1688_, 3);
v_commitIndependentGoals_1707_ = lean_ctor_get_uint8(v_toBacktrackConfig_1688_, sizeof(void*)*4);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_toBacktrackConfig_1688_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1709_ = v_toBacktrackConfig_1688_;
v_isShared_1710_ = v_isSharedCheck_1721_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_discharge_1706_);
lean_inc(v_suspend_1705_);
lean_inc(v_proc_1704_);
lean_inc(v_maxDepth_1703_);
lean_dec(v_toBacktrackConfig_1688_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1721_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___f_1711_; lean_object* v___x_1713_; 
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1711_, 0, v_discharge_1686_);
lean_closure_set(v___f_1711_, 1, v_discharge_1706_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 3, v___f_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_maxDepth_1703_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_proc_1704_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_suspend_1705_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v___f_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*4, v_commitIndependentGoals_1707_);
v___x_1713_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1713_);
v___x_1715_ = v___x_1701_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_toApplyConfig_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*2, v_transparency_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*2 + 1, v_symm_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*2 + 2, v_exfalso_1699_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1715_);
v___x_1717_ = v___x_1694_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*1, v_backtracking_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*1 + 1, v_intro_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*1 + 2, v_constructor_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*1 + 3, v_suggestions_1692_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = 1;
v___x_1733_ = l_Lean_Meta_intro1Core(v_g_1726_, v___x_1732_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1752_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1752_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1752_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1750_; 
v_snd_1738_ = lean_ctor_get(v_a_1734_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_a_1734_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v_a_1734_, 0);
lean_dec(v_unused_1751_);
v___x_1740_ = v_a_1734_;
v_isShared_1741_ = v_isSharedCheck_1750_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_dec(v_a_1734_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1750_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = lean_box(0);
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 1);
lean_ctor_set(v___x_1740_, 1, v___x_1742_);
lean_ctor_set(v___x_1740_, 0, v_snd_1738_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_snd_1738_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1745_);
v___x_1747_ = v___x_1736_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
v_a_1753_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1733_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1733_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1769_){
_start:
{
lean_object* v___f_1770_; lean_object* v___x_1771_; 
v___f_1770_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1771_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1769_, v___f_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1783_ = l_Lean_MVarId_constructor(v_g_1776_, v___x_1782_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1792_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1783_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1783_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1809_){
_start:
{
lean_object* v___f_1810_; lean_object* v___x_1811_; 
v___f_1810_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1811_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1809_, v___f_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
lean_inc(v_g_1814_);
v___x_1820_ = l_Lean_MVarId_getType(v_g_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = lean_box(0);
v___x_1823_ = l_Lean_Meta_synthInstance(v_a_1821_, v___x_1822_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1833_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1814_, v_a_1824_, v___y_1816_);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v___x_1825_, 0);
lean_dec(v_unused_1834_);
v___x_1827_ = v___x_1825_;
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v___x_1825_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1833_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_g_1814_);
v_a_1835_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1823_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1823_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_g_1814_);
v_a_1843_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1820_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1820_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1859_){
_start:
{
lean_object* v___f_1860_; lean_object* v___x_1861_; 
v___f_1860_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1861_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1859_, v___f_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = l_Lean_Expr_hasMVar(v_e_1862_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_e_1862_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v_mctx_1868_; lean_object* v___x_1869_; lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___x_1872_; lean_object* v_cache_1873_; lean_object* v_zetaDeltaFVarIds_1874_; lean_object* v_postponed_1875_; lean_object* v_diag_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1885_; 
v___x_1867_ = lean_st_ref_get(v___y_1863_);
v_mctx_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_mctx_1868_);
lean_dec(v___x_1867_);
v___x_1869_ = l_Lean_instantiateMVarsCore(v_mctx_1868_, v_e_1862_);
v_fst_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_fst_1870_);
v_snd_1871_ = lean_ctor_get(v___x_1869_, 1);
lean_inc(v_snd_1871_);
lean_dec_ref(v___x_1869_);
v___x_1872_ = lean_st_ref_take(v___y_1863_);
v_cache_1873_ = lean_ctor_get(v___x_1872_, 1);
v_zetaDeltaFVarIds_1874_ = lean_ctor_get(v___x_1872_, 2);
v_postponed_1875_ = lean_ctor_get(v___x_1872_, 3);
v_diag_1876_ = lean_ctor_get(v___x_1872_, 4);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v___x_1872_, 0);
lean_dec(v_unused_1886_);
v___x_1878_ = v___x_1872_;
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_diag_1876_);
lean_inc(v_postponed_1875_);
lean_inc(v_zetaDeltaFVarIds_1874_);
lean_inc(v_cache_1873_);
lean_dec(v___x_1872_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1885_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v_snd_1871_);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_snd_1871_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_cache_1873_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_zetaDeltaFVarIds_1874_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_postponed_1875_);
lean_ctor_set(v_reuseFailAlloc_1884_, 4, v_diag_1876_);
v___x_1881_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_st_ref_set(v___y_1863_, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_fst_1870_);
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1887_, v___y_1888_);
lean_dec(v___y_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1891_, v___y_1893_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1905_, v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1921_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1912_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1912_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1929_, v_x_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1937_, lean_object* v_mvarId_1938_, lean_object* v_x_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_mvarId_1947_, lean_object* v_x_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1946_, v_mvarId_1947_, v_x_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_ref_1961_; lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_ref_1961_ = lean_ctor_get(v___y_1958_, 5);
v___x_1962_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
lean_inc(v_ref_1961_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_ref_1961_);
lean_ctor_set(v___x_1967_, 1, v_a_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 1);
lean_ctor_set(v___x_1965_, 0, v___x_1967_);
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
if (lean_obj_tag(v_x_1979_) == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = l_List_reverse___redArg(v_x_1980_);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
else
{
lean_object* v_head_1988_; lean_object* v_tail_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2009_; 
v_head_1988_ = lean_ctor_get(v_x_1979_, 0);
v_tail_1989_ = lean_ctor_get(v_x_1979_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_x_1979_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1991_ = v_x_1979_;
v_isShared_1992_ = v_isSharedCheck_2009_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_tail_1989_);
lean_inc(v_head_1988_);
lean_dec(v_x_1979_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2009_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_inc(v_head_1988_);
v___x_1993_ = l_Lean_Expr_mvar___override(v_head_1988_);
v___x_1994_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1994_, 0, v___x_1993_);
v___x_1995_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1988_, v___x_1994_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1995_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 1, v_x_1980_);
lean_ctor_set(v___x_1991_, 0, v_a_1996_);
v___x_1998_ = v___x_1991_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1996_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_x_1980_);
v___x_1998_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
v_x_1979_ = v_tail_1989_;
v_x_1980_ = v___x_1998_;
goto _start;
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_del_object(v___x_1991_);
lean_dec(v_tail_1989_);
lean_dec(v_x_1980_);
v_a_2001_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1995_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1995_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2010_, v_x_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2017_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2021_, lean_object* v_proc_2022_, lean_object* v_orig_2023_, lean_object* v_goals_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_box(0);
lean_inc(v_orig_2023_);
v___x_2031_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2023_, v___x_2030_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2031_);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
v___x_2033_ = lean_apply_6(v_test_2021_, v_a_2032_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; uint8_t v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = lean_unbox(v_a_2034_);
lean_dec(v_a_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_goals_2024_);
lean_dec(v_orig_2023_);
lean_dec_ref(v_proc_2022_);
v___x_2036_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2037_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2036_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v___x_2046_; 
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
v___x_2046_ = lean_apply_7(v_proc_2022_, v_orig_2023_, v_goals_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, lean_box(0));
return v___x_2046_;
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_goals_2024_);
lean_dec(v_orig_2023_);
lean_dec_ref(v_proc_2022_);
v_a_2047_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2033_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2033_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_goals_2024_);
lean_dec(v_orig_2023_);
lean_dec_ref(v_proc_2022_);
lean_dec_ref(v_test_2021_);
v_a_2055_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2031_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2031_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2063_, lean_object* v_proc_2064_, lean_object* v_orig_2065_, lean_object* v_goals_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2063_, v_proc_2064_, v_orig_2065_, v_goals_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2073_, lean_object* v_test_2074_){
_start:
{
lean_object* v_toApplyRulesConfig_2075_; lean_object* v_toBacktrackConfig_2076_; uint8_t v_backtracking_2077_; uint8_t v_intro_2078_; uint8_t v_constructor_2079_; uint8_t v_suggestions_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2112_; 
v_toApplyRulesConfig_2075_ = lean_ctor_get(v_cfg_2073_, 0);
lean_inc_ref(v_toApplyRulesConfig_2075_);
v_toBacktrackConfig_2076_ = lean_ctor_get(v_toApplyRulesConfig_2075_, 0);
lean_inc_ref(v_toBacktrackConfig_2076_);
v_backtracking_2077_ = lean_ctor_get_uint8(v_cfg_2073_, sizeof(void*)*1);
v_intro_2078_ = lean_ctor_get_uint8(v_cfg_2073_, sizeof(void*)*1 + 1);
v_constructor_2079_ = lean_ctor_get_uint8(v_cfg_2073_, sizeof(void*)*1 + 2);
v_suggestions_2080_ = lean_ctor_get_uint8(v_cfg_2073_, sizeof(void*)*1 + 3);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_cfg_2073_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v_cfg_2073_, 0);
lean_dec(v_unused_2113_);
v___x_2082_ = v_cfg_2073_;
v_isShared_2083_ = v_isSharedCheck_2112_;
goto v_resetjp_2081_;
}
else
{
lean_dec(v_cfg_2073_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2112_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_toApplyConfig_2084_; uint8_t v_transparency_2085_; uint8_t v_symm_2086_; uint8_t v_exfalso_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2110_; 
v_toApplyConfig_2084_ = lean_ctor_get(v_toApplyRulesConfig_2075_, 1);
v_transparency_2085_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2075_, sizeof(void*)*2);
v_symm_2086_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2075_, sizeof(void*)*2 + 1);
v_exfalso_2087_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2075_, sizeof(void*)*2 + 2);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_toApplyRulesConfig_2075_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_toApplyRulesConfig_2075_, 0);
lean_dec(v_unused_2111_);
v___x_2089_ = v_toApplyRulesConfig_2075_;
v_isShared_2090_ = v_isSharedCheck_2110_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_toApplyConfig_2084_);
lean_dec(v_toApplyRulesConfig_2075_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2110_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_maxDepth_2091_; lean_object* v_proc_2092_; lean_object* v_suspend_2093_; lean_object* v_discharge_2094_; uint8_t v_commitIndependentGoals_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2109_; 
v_maxDepth_2091_ = lean_ctor_get(v_toBacktrackConfig_2076_, 0);
v_proc_2092_ = lean_ctor_get(v_toBacktrackConfig_2076_, 1);
v_suspend_2093_ = lean_ctor_get(v_toBacktrackConfig_2076_, 2);
v_discharge_2094_ = lean_ctor_get(v_toBacktrackConfig_2076_, 3);
v_commitIndependentGoals_2095_ = lean_ctor_get_uint8(v_toBacktrackConfig_2076_, sizeof(void*)*4);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_toBacktrackConfig_2076_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2097_ = v_toBacktrackConfig_2076_;
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_discharge_2094_);
lean_inc(v_suspend_2093_);
lean_inc(v_proc_2092_);
lean_inc(v_maxDepth_2091_);
lean_dec(v_toBacktrackConfig_2076_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___f_2099_; lean_object* v___x_2101_; 
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2099_, 0, v_test_2074_);
lean_closure_set(v___f_2099_, 1, v_proc_2092_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___f_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_maxDepth_2091_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___f_2099_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_suspend_2093_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_discharge_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*4, v_commitIndependentGoals_2095_);
v___x_2101_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2101_);
v___x_2103_ = v___x_2089_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_toApplyConfig_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*2, v_transparency_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*2 + 1, v_symm_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*2 + 2, v_exfalso_2087_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2103_);
v___x_2105_ = v___x_2082_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*1, v_backtracking_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*1 + 1, v_intro_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*1 + 2, v_constructor_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*1 + 3, v_suggestions_2080_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2114_, lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2122_, lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2122_, v_msg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2131_, lean_object* v_sols_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0));
lean_inc(v_sols_2132_);
v___x_2139_ = l_List_any___redArg(v_sols_2132_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_inc(v___y_2136_);
lean_inc_ref(v___y_2135_);
lean_inc(v___y_2134_);
lean_inc_ref(v___y_2133_);
v___x_2140_ = lean_apply_6(v_test_2131_, v_sols_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, lean_box(0));
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_sols_2132_);
lean_dec_ref(v_test_2131_);
v___x_2141_ = lean_box(v___x_2139_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2143_, lean_object* v_sols_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2143_, v_sols_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2151_, lean_object* v_test_2152_){
_start:
{
lean_object* v___f_2153_; lean_object* v___x_2154_; 
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2153_, 0, v_test_2152_);
v___x_2154_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2151_, v___f_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_e_2155_, lean_object* v_s_2156_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = l_Lean_Expr_occurs(v_e_2155_, v_s_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_e_2158_, lean_object* v_s_2159_){
_start:
{
uint8_t v_res_2160_; lean_object* v_r_2161_; 
v_res_2160_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_e_2158_, v_s_2159_);
lean_dec_ref(v_s_2159_);
v_r_2161_ = lean_box(v_res_2160_);
return v_r_2161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object* v_sols_2162_, lean_object* v_e_2163_){
_start:
{
lean_object* v___f_2164_; uint8_t v___x_2165_; 
v___f_2164_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2164_, 0, v_e_2163_);
v___x_2165_ = l_List_any___redArg(v_sols_2162_, v___f_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object* v_sols_2166_, lean_object* v_e_2167_){
_start:
{
uint8_t v_res_2168_; lean_object* v_r_2169_; 
v_res_2168_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(v_sols_2166_, v_e_2167_);
v_r_2169_ = lean_box(v_res_2168_);
return v_r_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object* v_use_2170_, lean_object* v_sols_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___f_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2177_, 0, v_sols_2171_);
v___x_2178_ = l_List_all___redArg(v_use_2170_, v___f_2177_);
v___x_2179_ = lean_box(v___x_2178_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object* v_use_2181_, lean_object* v_sols_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(v_use_2181_, v_sols_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2189_, lean_object* v_use_2190_){
_start:
{
lean_object* v___f_2191_; lean_object* v___x_2192_; 
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2191_, 0, v_use_2190_);
v___x_2192_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2189_, v___f_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2193_){
_start:
{
lean_object* v___y_2195_; lean_object* v_toApplyRulesConfig_2196_; uint8_t v_backtracking_2197_; uint8_t v_intro_2198_; uint8_t v_constructor_2199_; uint8_t v_suggestions_2200_; uint8_t v_intro_2204_; 
v_intro_2204_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1 + 1);
if (v_intro_2204_ == 0)
{
lean_object* v_toApplyRulesConfig_2205_; uint8_t v_backtracking_2206_; uint8_t v_constructor_2207_; uint8_t v_suggestions_2208_; 
v_toApplyRulesConfig_2205_ = lean_ctor_get(v_cfg_2193_, 0);
lean_inc_ref(v_toApplyRulesConfig_2205_);
v_backtracking_2206_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1);
v_constructor_2207_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1 + 2);
v_suggestions_2208_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1 + 3);
v___y_2195_ = v_cfg_2193_;
v_toApplyRulesConfig_2196_ = v_toApplyRulesConfig_2205_;
v_backtracking_2197_ = v_backtracking_2206_;
v_intro_2198_ = v_intro_2204_;
v_constructor_2199_ = v_constructor_2207_;
v_suggestions_2200_ = v_suggestions_2208_;
goto v___jp_2194_;
}
else
{
lean_object* v_toApplyRulesConfig_2209_; uint8_t v_backtracking_2210_; uint8_t v_constructor_2211_; uint8_t v_suggestions_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2226_; 
v_toApplyRulesConfig_2209_ = lean_ctor_get(v_cfg_2193_, 0);
v_backtracking_2210_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1);
v_constructor_2211_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1 + 2);
v_suggestions_2212_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*1 + 3);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_cfg_2193_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2214_ = v_cfg_2193_;
v_isShared_2215_ = v_isSharedCheck_2226_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_toApplyRulesConfig_2209_);
lean_dec(v_cfg_2193_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2226_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
uint8_t v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = 0;
if (v_isShared_2215_ == 0)
{
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_toApplyRulesConfig_2209_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*1, v_backtracking_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*1 + 2, v_constructor_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2225_, sizeof(void*)*1 + 3, v_suggestions_2212_);
v___x_2218_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v_toApplyRulesConfig_2220_; uint8_t v_backtracking_2221_; uint8_t v_intro_2222_; uint8_t v_constructor_2223_; uint8_t v_suggestions_2224_; 
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*1 + 1, v___x_2216_);
v___x_2219_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2218_);
v_toApplyRulesConfig_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc_ref(v_toApplyRulesConfig_2220_);
v_backtracking_2221_ = lean_ctor_get_uint8(v___x_2219_, sizeof(void*)*1);
v_intro_2222_ = lean_ctor_get_uint8(v___x_2219_, sizeof(void*)*1 + 1);
v_constructor_2223_ = lean_ctor_get_uint8(v___x_2219_, sizeof(void*)*1 + 2);
v_suggestions_2224_ = lean_ctor_get_uint8(v___x_2219_, sizeof(void*)*1 + 3);
v___y_2195_ = v___x_2219_;
v_toApplyRulesConfig_2196_ = v_toApplyRulesConfig_2220_;
v_backtracking_2197_ = v_backtracking_2221_;
v_intro_2198_ = v_intro_2222_;
v_constructor_2199_ = v_constructor_2223_;
v_suggestions_2200_ = v_suggestions_2224_;
goto v___jp_2194_;
}
}
}
v___jp_2194_:
{
if (v_constructor_2199_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2196_);
return v___y_2195_;
}
else
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec_ref(v___y_2195_);
v___x_2201_ = 0;
v___x_2202_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2202_, 0, v_toApplyRulesConfig_2196_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1, v_backtracking_2197_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1 + 1, v_intro_2198_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1 + 2, v___x_2201_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1 + 3, v_suggestions_2200_);
v___x_2203_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2202_);
return v___x_2203_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
if (lean_obj_tag(v_x_2227_) == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = l_List_reverse___redArg(v_x_2228_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
else
{
lean_object* v_head_2238_; lean_object* v_tail_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2257_; 
v_head_2238_ = lean_ctor_get(v_x_2227_, 0);
v_tail_2239_ = lean_ctor_get(v_x_2227_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_x_2227_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2241_ = v_x_2227_;
v_isShared_2242_ = v_isSharedCheck_2257_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_tail_2239_);
lean_inc(v_head_2238_);
lean_dec(v_x_2227_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2257_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; 
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
lean_inc(v___y_2230_);
lean_inc_ref(v___y_2229_);
v___x_2243_ = lean_apply_7(v_head_2238_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, lean_box(0));
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v_x_2228_);
lean_ctor_set(v___x_2241_, 0, v_a_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2244_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_x_2228_);
v___x_2246_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
v_x_2227_ = v_tail_2239_;
v_x_2228_ = v___x_2246_;
goto _start;
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_del_object(v___x_2241_);
lean_dec(v_tail_2239_);
lean_dec(v_x_2228_);
v_a_2249_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2243_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2243_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2258_, lean_object* v_x_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2258_, v_x_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2268_, lean_object* v_cfg_2269_, lean_object* v_lemmas_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
v___x_2278_ = lean_apply_8(v_ctx_2268_, v_cfg_2269_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, lean_box(0));
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref(v___x_2278_);
v___x_2280_ = lean_box(0);
v___x_2281_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2270_, v___x_2280_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = l_List_appendTR___redArg(v_a_2279_, v_a_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_dec(v_a_2279_);
return v___x_2281_;
}
}
else
{
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v_lemmas_2270_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2291_, lean_object* v_cfg_2292_, lean_object* v_lemmas_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2291_, v_cfg_2292_, v_lemmas_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2302_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = 0;
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2304_){
_start:
{
uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_res_2305_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2304_);
lean_dec(v_x_2304_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2307_, lean_object* v___x_2308_, lean_object* v___x_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2307_, v___x_2308_, v___x_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_fst_2320_; lean_object* v___x_2322_; 
v_fst_2320_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_fst_2320_);
lean_dec(v_a_2316_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_fst_2320_);
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
v_a_2325_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2315_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2315_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2333_, lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2333_, v___x_2334_, v___x_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2356_, lean_object* v_g_2357_, lean_object* v_lemmas_2358_, lean_object* v_ctx_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; 
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2365_, 0, v_ctx_2359_);
lean_closure_set(v___f_2365_, 1, v_cfg_2356_);
lean_closure_set(v___f_2365_, 2, v_lemmas_2358_);
v___x_2366_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2367_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2368_, 0, v___f_2365_);
lean_closure_set(v___f_2368_, 1, v___x_2366_);
lean_closure_set(v___f_2368_, 2, v___x_2367_);
v___x_2369_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2357_, v___f_2368_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2370_, lean_object* v_g_2371_, lean_object* v_lemmas_2372_, lean_object* v_ctx_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2370_, v_g_2371_, v_lemmas_2372_, v_ctx_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2380_, lean_object* v_lemmas_2381_, lean_object* v_ctx_2382_, lean_object* v_g_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; 
lean_inc(v_g_2383_);
lean_inc_ref(v_cfg_2380_);
v___x_2389_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2380_, v_g_2383_, v_lemmas_2381_, v_ctx_2382_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_toApplyRulesConfig_2390_; lean_object* v_a_2391_; lean_object* v_toApplyConfig_2392_; uint8_t v_transparency_2393_; lean_object* v___x_2394_; 
v_toApplyRulesConfig_2390_ = lean_ctor_get(v_cfg_2380_, 0);
lean_inc_ref(v_toApplyRulesConfig_2390_);
lean_dec_ref(v_cfg_2380_);
v_a_2391_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2389_);
v_toApplyConfig_2392_ = lean_ctor_get(v_toApplyRulesConfig_2390_, 1);
lean_inc_ref(v_toApplyConfig_2392_);
v_transparency_2393_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2390_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2390_);
v___x_2394_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2392_, v_transparency_2393_, v_a_2391_, v_g_2383_, v_a_2385_, v_a_2387_);
return v___x_2394_;
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_g_2383_);
lean_dec_ref(v_cfg_2380_);
v_a_2395_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2389_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2389_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2403_, lean_object* v_lemmas_2404_, lean_object* v_ctx_2405_, lean_object* v_g_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2403_, v_lemmas_2404_, v_ctx_2405_, v_g_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2413_, lean_object* v_lemmas_2414_, lean_object* v_ctx_2415_, lean_object* v_g_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; 
lean_inc(v_g_2416_);
lean_inc_ref(v_cfg_2413_);
v___x_2422_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2413_, v_g_2416_, v_lemmas_2414_, v_ctx_2415_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_toApplyRulesConfig_2423_; lean_object* v_a_2424_; lean_object* v_toApplyConfig_2425_; uint8_t v_transparency_2426_; lean_object* v___x_2427_; 
v_toApplyRulesConfig_2423_ = lean_ctor_get(v_cfg_2413_, 0);
lean_inc_ref(v_toApplyRulesConfig_2423_);
lean_dec_ref(v_cfg_2413_);
v_a_2424_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2422_);
v_toApplyConfig_2425_ = lean_ctor_get(v_toApplyRulesConfig_2423_, 1);
lean_inc_ref(v_toApplyConfig_2425_);
v_transparency_2426_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2423_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2423_);
v___x_2427_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2425_, v_transparency_2426_, v_a_2424_, v_g_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
return v___x_2427_;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_g_2416_);
lean_dec_ref(v_cfg_2413_);
v_a_2428_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2422_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2422_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2436_, lean_object* v_lemmas_2437_, lean_object* v_ctx_2438_, lean_object* v_g_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2436_, v_lemmas_2437_, v_ctx_2438_, v_g_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2445_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2446_, lean_object* v_i_2447_, lean_object* v_k_2448_){
_start:
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = lean_array_get_size(v_keys_2446_);
v___x_2450_ = lean_nat_dec_lt(v_i_2447_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_dec(v_i_2447_);
return v___x_2450_;
}
else
{
lean_object* v_k_x27_2451_; uint8_t v___x_2452_; 
v_k_x27_2451_ = lean_array_fget_borrowed(v_keys_2446_, v_i_2447_);
v___x_2452_ = l_Lean_instBEqMVarId_beq(v_k_2448_, v_k_x27_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = lean_nat_add(v_i_2447_, v___x_2453_);
lean_dec(v_i_2447_);
v_i_2447_ = v___x_2454_;
goto _start;
}
else
{
lean_dec(v_i_2447_);
return v___x_2452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2456_, lean_object* v_i_2457_, lean_object* v_k_2458_){
_start:
{
uint8_t v_res_2459_; lean_object* v_r_2460_; 
v_res_2459_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2456_, v_i_2457_, v_k_2458_);
lean_dec(v_k_2458_);
lean_dec_ref(v_keys_2456_);
v_r_2460_ = lean_box(v_res_2459_);
return v_r_2460_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2461_, size_t v_x_2462_, lean_object* v_x_2463_){
_start:
{
if (lean_obj_tag(v_x_2461_) == 0)
{
lean_object* v_es_2464_; lean_object* v___x_2465_; size_t v___x_2466_; size_t v___x_2467_; size_t v___x_2468_; lean_object* v_j_2469_; lean_object* v___x_2470_; 
v_es_2464_ = lean_ctor_get(v_x_2461_, 0);
v___x_2465_ = lean_box(2);
v___x_2466_ = ((size_t)5ULL);
v___x_2467_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2468_ = lean_usize_land(v_x_2462_, v___x_2467_);
v_j_2469_ = lean_usize_to_nat(v___x_2468_);
v___x_2470_ = lean_array_get_borrowed(v___x_2465_, v_es_2464_, v_j_2469_);
lean_dec(v_j_2469_);
switch(lean_obj_tag(v___x_2470_))
{
case 0:
{
lean_object* v_key_2471_; uint8_t v___x_2472_; 
v_key_2471_ = lean_ctor_get(v___x_2470_, 0);
v___x_2472_ = l_Lean_instBEqMVarId_beq(v_x_2463_, v_key_2471_);
return v___x_2472_;
}
case 1:
{
lean_object* v_node_2473_; size_t v___x_2474_; 
v_node_2473_ = lean_ctor_get(v___x_2470_, 0);
v___x_2474_ = lean_usize_shift_right(v_x_2462_, v___x_2466_);
v_x_2461_ = v_node_2473_;
v_x_2462_ = v___x_2474_;
goto _start;
}
default: 
{
uint8_t v___x_2476_; 
v___x_2476_ = 0;
return v___x_2476_;
}
}
}
else
{
lean_object* v_ks_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_ks_2477_ = lean_ctor_get(v_x_2461_, 0);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2477_, v___x_2478_, v_x_2463_);
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2480_, lean_object* v_x_2481_, lean_object* v_x_2482_){
_start:
{
size_t v_x_2218__boxed_2483_; uint8_t v_res_2484_; lean_object* v_r_2485_; 
v_x_2218__boxed_2483_ = lean_unbox_usize(v_x_2481_);
lean_dec(v_x_2481_);
v_res_2484_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2480_, v_x_2218__boxed_2483_, v_x_2482_);
lean_dec(v_x_2482_);
lean_dec_ref(v_x_2480_);
v_r_2485_ = lean_box(v_res_2484_);
return v_r_2485_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2486_, lean_object* v_x_2487_){
_start:
{
uint64_t v___x_2488_; size_t v___x_2489_; uint8_t v___x_2490_; 
v___x_2488_ = l_Lean_instHashableMVarId_hash(v_x_2487_);
v___x_2489_ = lean_uint64_to_usize(v___x_2488_);
v___x_2490_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2486_, v___x_2489_, v_x_2487_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2491_, lean_object* v_x_2492_){
_start:
{
uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_res_2493_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec_ref(v_x_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; lean_object* v_mctx_2499_; lean_object* v_eAssignment_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2498_ = lean_st_ref_get(v___y_2496_);
v_mctx_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc_ref(v_mctx_2499_);
lean_dec(v___x_2498_);
v_eAssignment_2500_ = lean_ctor_get(v_mctx_2499_, 7);
lean_inc_ref(v_eAssignment_2500_);
lean_dec_ref(v_mctx_2499_);
v___x_2501_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2500_, v_mvarId_2495_);
lean_dec_ref(v_eAssignment_2500_);
v___x_2502_ = lean_box(v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec(v_mvarId_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2508_, lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
return v_x_2508_;
}
else
{
lean_object* v_head_2510_; lean_object* v_tail_2511_; lean_object* v___x_2512_; 
v_head_2510_ = lean_ctor_get(v_x_2509_, 0);
lean_inc(v_head_2510_);
v_tail_2511_ = lean_ctor_get(v_x_2509_, 1);
lean_inc(v_tail_2511_);
lean_dec_ref(v_x_2509_);
v___x_2512_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2508_, v_head_2510_);
v_x_2508_ = v___x_2512_;
v_x_2509_ = v_tail_2511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2514_, lean_object* v_a_2515_, uint8_t v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
if (lean_obj_tag(v_a_2517_) == 0)
{
if (lean_obj_tag(v_a_2518_) == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v_a_2515_);
lean_dec_ref(v_f_2514_);
v___x_2525_ = lean_box(v_a_2516_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
lean_ctor_set(v___x_2526_, 1, v_a_2519_);
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
else
{
lean_object* v_head_2528_; lean_object* v_tail_2529_; 
v_head_2528_ = lean_ctor_get(v_a_2518_, 0);
lean_inc(v_head_2528_);
v_tail_2529_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_tail_2529_);
lean_dec_ref(v_a_2518_);
v_a_2517_ = v_head_2528_;
v_a_2518_ = v_tail_2529_;
goto _start;
}
}
else
{
lean_object* v_head_2531_; lean_object* v_tail_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2575_; 
v_head_2531_ = lean_ctor_get(v_a_2517_, 0);
v_tail_2532_ = lean_ctor_get(v_a_2517_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_a_2517_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2534_ = v_a_2517_;
v_isShared_2535_ = v_isSharedCheck_2575_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_tail_2532_);
lean_inc(v_head_2531_);
lean_dec(v_a_2517_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2575_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2574_; 
v___x_2536_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2531_, v___y_2521_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2574_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2574_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
if (v___x_2541_ == 0)
{
lean_object* v_zero_2542_; uint8_t v_isZero_2543_; 
v_zero_2542_ = lean_unsigned_to_nat(0u);
v_isZero_2543_ = lean_nat_dec_eq(v_a_2515_, v_zero_2542_);
if (v_isZero_2543_ == 1)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
lean_del_object(v___x_2534_);
lean_dec(v_a_2515_);
lean_dec_ref(v_f_2514_);
v___x_2544_ = lean_array_push(v_a_2519_, v_head_2531_);
v___x_2545_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2544_, v_tail_2532_);
v___x_2546_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2545_, v_a_2518_);
v___x_2547_ = lean_box(v_a_2516_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___x_2546_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2548_);
v___x_2550_ = v___x_2539_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_del_object(v___x_2539_);
lean_inc_ref(v_f_2514_);
lean_inc(v_head_2531_);
v___x_2552_ = lean_apply_1(v_f_2514_, v_head_2531_);
v___x_2553_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2552_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v_one_2555_; lean_object* v_n_2556_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v_one_2555_ = lean_unsigned_to_nat(1u);
v_n_2556_ = lean_nat_sub(v_a_2515_, v_one_2555_);
lean_dec(v_a_2515_);
if (lean_obj_tag(v_a_2554_) == 0)
{
lean_object* v___x_2557_; 
lean_del_object(v___x_2534_);
v___x_2557_ = lean_array_push(v_a_2519_, v_head_2531_);
v_a_2515_ = v_n_2556_;
v_a_2517_ = v_tail_2532_;
v_a_2519_ = v___x_2557_;
goto _start;
}
else
{
lean_object* v_val_2559_; uint8_t v___x_2560_; lean_object* v___x_2562_; 
lean_dec(v_head_2531_);
v_val_2559_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_val_2559_);
lean_dec_ref(v_a_2554_);
v___x_2560_ = 1;
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v_a_2518_);
lean_ctor_set(v___x_2534_, 0, v_tail_2532_);
v___x_2562_ = v___x_2534_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_tail_2532_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_a_2518_);
v___x_2562_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
v_a_2515_ = v_n_2556_;
v_a_2516_ = v___x_2560_;
v_a_2517_ = v_val_2559_;
v_a_2518_ = v___x_2562_;
goto _start;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_del_object(v___x_2534_);
lean_dec(v_tail_2532_);
lean_dec(v_head_2531_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_a_2515_);
lean_dec_ref(v_f_2514_);
v_a_2565_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2553_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2553_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
else
{
lean_del_object(v___x_2539_);
lean_del_object(v___x_2534_);
lean_dec(v_head_2531_);
v_a_2517_ = v_tail_2532_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
uint8_t v_a_2299__boxed_2587_; lean_object* v_res_2588_; 
v_a_2299__boxed_2587_ = lean_unbox(v_a_2578_);
v_res_2588_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2576_, v_a_2577_, v_a_2299__boxed_2587_, v_a_2579_, v_a_2580_, v_a_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2589_, size_t v_i_2590_, size_t v_stop_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_a_2599_; uint8_t v___x_2603_; 
v___x_2603_ = lean_usize_dec_eq(v_i_2590_, v_stop_2591_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2607_; 
v___x_2604_ = lean_array_uget_borrowed(v_as_2589_, v_i_2590_);
v___x_2607_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2604_, v___y_2594_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; uint8_t v___x_2609_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = lean_unbox(v_a_2608_);
lean_dec(v_a_2608_);
if (v___x_2609_ == 0)
{
goto v___jp_2605_;
}
else
{
v_a_2599_ = v_b_2592_;
goto v___jp_2598_;
}
}
else
{
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2610_; uint8_t v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2607_);
v___x_2611_ = lean_unbox(v_a_2610_);
lean_dec(v_a_2610_);
if (v___x_2611_ == 0)
{
v_a_2599_ = v_b_2592_;
goto v___jp_2598_;
}
else
{
goto v___jp_2605_;
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_b_2592_);
v_a_2612_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2607_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2607_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
v___jp_2605_:
{
lean_object* v___x_2606_; 
lean_inc(v___x_2604_);
v___x_2606_ = lean_array_push(v_b_2592_, v___x_2604_);
v_a_2599_ = v___x_2606_;
goto v___jp_2598_;
}
}
else
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v_b_2592_);
return v___x_2620_;
}
v___jp_2598_:
{
size_t v___x_2600_; size_t v___x_2601_; 
v___x_2600_ = ((size_t)1ULL);
v___x_2601_ = lean_usize_add(v_i_2590_, v___x_2600_);
v_i_2590_ = v___x_2601_;
v_b_2592_ = v_a_2599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2621_, lean_object* v_i_2622_, lean_object* v_stop_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
size_t v_i_boxed_2630_; size_t v_stop_boxed_2631_; lean_object* v_res_2632_; 
v_i_boxed_2630_ = lean_unbox_usize(v_i_2622_);
lean_dec(v_i_2622_);
v_stop_boxed_2631_ = lean_unbox_usize(v_stop_2623_);
lean_dec(v_stop_2623_);
v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2621_, v_i_boxed_2630_, v_stop_boxed_2631_, v_b_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec_ref(v_as_2621_);
return v_res_2632_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2636_ = lean_array_to_list(v___x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2637_, lean_object* v_goals_2638_, lean_object* v_maxIters_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2645_ = 0;
v___x_2646_ = lean_box(0);
v___x_2647_ = lean_unsigned_to_nat(0u);
v___x_2648_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2649_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2637_, v_maxIters_2639_, v___x_2645_, v_goals_2638_, v___x_2646_, v___x_2648_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2699_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2699_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2699_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_fst_2654_; lean_object* v_snd_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2698_; 
v_fst_2654_ = lean_ctor_get(v_a_2650_, 0);
v_snd_2655_ = lean_ctor_get(v_a_2650_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2650_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2657_ = v_a_2650_;
v_isShared_2658_ = v_isSharedCheck_2698_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snd_2655_);
lean_inc(v_fst_2654_);
lean_dec(v_a_2650_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2698_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_____do__lift_2660_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = lean_array_get_size(v_snd_2655_);
v___x_2669_ = lean_nat_dec_lt(v___x_2647_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_del_object(v___x_2657_);
lean_dec(v_snd_2655_);
lean_del_object(v___x_2652_);
v___x_2670_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_fst_2654_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
else
{
uint8_t v___x_2673_; 
v___x_2673_ = lean_nat_dec_le(v___x_2668_, v___x_2668_);
if (v___x_2673_ == 0)
{
if (v___x_2669_ == 0)
{
lean_dec(v_snd_2655_);
v_____do__lift_2660_ = v___x_2648_;
goto v___jp_2659_;
}
else
{
size_t v___x_2674_; size_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = ((size_t)0ULL);
v___x_2675_ = lean_usize_of_nat(v___x_2668_);
v___x_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2655_, v___x_2674_, v___x_2675_, v___x_2648_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v_snd_2655_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v_____do__lift_2660_ = v_a_2677_;
goto v___jp_2659_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_del_object(v___x_2657_);
lean_dec(v_fst_2654_);
lean_del_object(v___x_2652_);
v_a_2678_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2676_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2676_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
else
{
size_t v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = ((size_t)0ULL);
v___x_2687_ = lean_usize_of_nat(v___x_2668_);
v___x_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2655_, v___x_2686_, v___x_2687_, v___x_2648_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v_snd_2655_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
v_____do__lift_2660_ = v_a_2689_;
goto v___jp_2659_;
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2657_);
lean_dec(v_fst_2654_);
lean_del_object(v___x_2652_);
v_a_2690_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2688_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = lean_array_to_list(v_____do__lift_2660_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2661_);
v___x_2663_ = v___x_2657_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_fst_2654_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2663_);
v___x_2665_ = v___x_2652_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_a_2700_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2649_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2649_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2708_, lean_object* v_goals_2709_, lean_object* v_maxIters_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2708_, v_goals_2709_, v_maxIters_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
return v_res_2716_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2719_ = l_Lean_stringToMessageData(v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2720_, lean_object* v_goals_2721_, lean_object* v_maxIters_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2720_, v_goals_2721_, v_maxIters_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2741_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2731_ = v___x_2728_;
v_isShared_2732_ = v_isSharedCheck_2741_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2741_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_fst_2733_; uint8_t v___x_2734_; 
v_fst_2733_ = lean_ctor_get(v_a_2729_, 0);
v___x_2734_ = lean_unbox(v_fst_2733_);
if (v___x_2734_ == 1)
{
lean_object* v_snd_2735_; lean_object* v___x_2737_; 
v_snd_2735_ = lean_ctor_get(v_a_2729_, 1);
lean_inc(v_snd_2735_);
lean_dec(v_a_2729_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_snd_2735_);
v___x_2737_ = v___x_2731_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_snd_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_del_object(v___x_2731_);
lean_dec(v_a_2729_);
v___x_2739_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2740_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2739_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
return v___x_2740_;
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
v_a_2742_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2728_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2728_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2750_, lean_object* v_goals_2751_, lean_object* v_maxIters_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2750_, v_goals_2751_, v_maxIters_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2759_, lean_object* v_ctx_2760_, lean_object* v_cfg_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
uint8_t v_backtracking_2768_; 
v_backtracking_2768_ = lean_ctor_get_uint8(v_cfg_2761_, sizeof(void*)*1);
if (v_backtracking_2768_ == 0)
{
lean_object* v_toApplyRulesConfig_2769_; lean_object* v_toBacktrackConfig_2770_; lean_object* v_maxDepth_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_toApplyRulesConfig_2769_ = lean_ctor_get(v_cfg_2761_, 0);
v_toBacktrackConfig_2770_ = lean_ctor_get(v_toApplyRulesConfig_2769_, 0);
v_maxDepth_2771_ = lean_ctor_get(v_toBacktrackConfig_2770_, 0);
lean_inc(v_maxDepth_2771_);
v___x_2772_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2772_, 0, v_cfg_2761_);
lean_closure_set(v___x_2772_, 1, v_lemmas_2759_);
lean_closure_set(v___x_2772_, 2, v_ctx_2760_);
v___x_2773_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2772_, v_a_2762_, v_maxDepth_2771_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
return v___x_2773_;
}
else
{
lean_object* v_toApplyRulesConfig_2774_; lean_object* v_toBacktrackConfig_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_toApplyRulesConfig_2774_ = lean_ctor_get(v_cfg_2761_, 0);
v_toBacktrackConfig_2775_ = lean_ctor_get(v_toApplyRulesConfig_2774_, 0);
lean_inc_ref(v_toBacktrackConfig_2775_);
v___x_2776_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2777_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2777_, 0, v_cfg_2761_);
lean_closure_set(v___x_2777_, 1, v_lemmas_2759_);
lean_closure_set(v___x_2777_, 2, v_ctx_2760_);
v___x_2778_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2775_, v___x_2776_, v___x_2777_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_);
return v___x_2778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2779_, lean_object* v_ctx_2780_, lean_object* v_cfg_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2779_, v_ctx_2780_, v_cfg_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2789_, v___y_2791_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v_mvarId_2796_);
return v_res_2802_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2803_, lean_object* v_x_2804_, lean_object* v_x_2805_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2804_, v_x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2807_, lean_object* v_x_2808_, lean_object* v_x_2809_){
_start:
{
uint8_t v_res_2810_; lean_object* v_r_2811_; 
v_res_2810_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2807_, v_x_2808_, v_x_2809_);
lean_dec(v_x_2809_);
lean_dec_ref(v_x_2808_);
v_r_2811_ = lean_box(v_res_2810_);
return v_r_2811_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2812_, lean_object* v_x_2813_, size_t v_x_2814_, lean_object* v_x_2815_){
_start:
{
uint8_t v___x_2816_; 
v___x_2816_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2813_, v_x_2814_, v_x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_){
_start:
{
size_t v_x_2759__boxed_2821_; uint8_t v_res_2822_; lean_object* v_r_2823_; 
v_x_2759__boxed_2821_ = lean_unbox_usize(v_x_2819_);
lean_dec(v_x_2819_);
v_res_2822_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2817_, v_x_2818_, v_x_2759__boxed_2821_, v_x_2820_);
lean_dec(v_x_2820_);
lean_dec_ref(v_x_2818_);
v_r_2823_ = lean_box(v_res_2822_);
return v_r_2823_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2824_, lean_object* v_keys_2825_, lean_object* v_vals_2826_, lean_object* v_heq_2827_, lean_object* v_i_2828_, lean_object* v_k_2829_){
_start:
{
uint8_t v___x_2830_; 
v___x_2830_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2825_, v_i_2828_, v_k_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2831_, lean_object* v_keys_2832_, lean_object* v_vals_2833_, lean_object* v_heq_2834_, lean_object* v_i_2835_, lean_object* v_k_2836_){
_start:
{
uint8_t v_res_2837_; lean_object* v_r_2838_; 
v_res_2837_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2831_, v_keys_2832_, v_vals_2833_, v_heq_2834_, v_i_2835_, v_k_2836_);
lean_dec(v_k_2836_);
lean_dec_ref(v_vals_2833_);
lean_dec_ref(v_keys_2832_);
v_r_2838_ = lean_box(v_res_2837_);
return v_r_2838_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec_ref(v_x_2850_);
return v_res_2856_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2859_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2860_ = l_Lean_Name_append(v___x_2859_, v___x_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2861_, lean_object* v_lemmas_2862_, lean_object* v_ctx_2863_, lean_object* v_goals_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_cfg_2870_; lean_object* v___x_2871_; 
v_cfg_2870_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2861_);
lean_inc(v_goals_2864_);
lean_inc_ref(v_cfg_2870_);
lean_inc_ref(v_ctx_2863_);
lean_inc(v_lemmas_2862_);
v___x_2871_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2862_, v_ctx_2863_, v_cfg_2870_, v_goals_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_dec_ref(v_cfg_2870_);
lean_dec(v_goals_2864_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
return v___x_2871_;
}
else
{
lean_object* v_a_2872_; lean_object* v___f_2873_; lean_object* v___y_2875_; uint8_t v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v_a_2882_; lean_object* v___y_2895_; uint8_t v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; uint8_t v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2905_; uint8_t v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; uint8_t v___y_2911_; lean_object* v_a_2912_; lean_object* v___y_2922_; uint8_t v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v_a_2929_; lean_object* v___y_2932_; uint8_t v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; uint8_t v___y_2938_; uint8_t v___y_2974_; uint8_t v___x_3027_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
v___f_2873_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3027_ = l_Lean_Exception_isInterrupt(v_a_2872_);
if (v___x_3027_ == 0)
{
uint8_t v___x_3028_; 
v___x_3028_ = l_Lean_Exception_isRuntime(v_a_2872_);
v___y_2974_ = v___x_3028_;
goto v___jp_2973_;
}
else
{
lean_dec(v_a_2872_);
v___y_2974_ = v___x_3027_;
goto v___jp_2973_;
}
v___jp_2874_:
{
lean_object* v___x_2883_; double v___x_2884_; double v___x_2885_; double v___x_2886_; double v___x_2887_; double v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2883_ = lean_io_mono_nanos_now();
v___x_2884_ = lean_float_of_nat(v___y_2879_);
v___x_2885_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2886_ = lean_float_div(v___x_2884_, v___x_2885_);
v___x_2887_ = lean_float_of_nat(v___x_2883_);
v___x_2888_ = lean_float_div(v___x_2887_, v___x_2885_);
v___x_2889_ = lean_box_float(v___x_2886_);
v___x_2890_ = lean_box_float(v___x_2888_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v_a_2882_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
lean_inc_ref(v___y_2875_);
lean_inc(v___y_2880_);
v___x_2893_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2880_, v___y_2876_, v___y_2875_, v___y_2877_, v___y_2881_, v___y_2878_, v___f_2873_, v___x_2892_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2893_;
}
v___jp_2894_:
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_a_2902_);
v___y_2875_ = v___y_2895_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2899_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___y_2900_;
v___y_2881_ = v___y_2901_;
v_a_2882_ = v___x_2903_;
goto v___jp_2874_;
}
v___jp_2904_:
{
lean_object* v___x_2913_; double v___x_2914_; double v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2913_ = lean_io_get_num_heartbeats();
v___x_2914_ = lean_float_of_nat(v___y_2907_);
v___x_2915_ = lean_float_of_nat(v___x_2913_);
v___x_2916_ = lean_box_float(v___x_2914_);
v___x_2917_ = lean_box_float(v___x_2915_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v_a_2912_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
lean_inc_ref(v___y_2905_);
lean_inc(v___y_2910_);
v___x_2920_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2910_, v___y_2906_, v___y_2905_, v___y_2908_, v___y_2911_, v___y_2909_, v___f_2873_, v___x_2919_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2920_;
}
v___jp_2921_:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v_a_2929_);
v___y_2905_ = v___y_2922_;
v___y_2906_ = v___y_2923_;
v___y_2907_ = v___y_2924_;
v___y_2908_ = v___y_2925_;
v___y_2909_ = v___y_2926_;
v___y_2910_ = v___y_2927_;
v___y_2911_ = v___y_2928_;
v_a_2912_ = v___x_2930_;
goto v___jp_2904_;
}
v___jp_2931_:
{
lean_object* v___x_2939_; lean_object* v_a_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2939_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2868_);
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2942_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2936_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = lean_io_mono_nanos_now();
v___x_2944_ = l_Lean_MVarId_exfalso(v___y_2934_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2946_, 0, v_a_2945_);
lean_ctor_set(v___x_2946_, 1, v___y_2935_);
v___x_2947_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2862_, v_ctx_2863_, v_cfg_2870_, v___x_2946_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set_tag(v___x_2950_, 1);
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
v___y_2875_ = v___y_2932_;
v___y_2876_ = v___y_2933_;
v___y_2877_ = v___y_2936_;
v___y_2878_ = v_a_2940_;
v___y_2879_ = v___x_2943_;
v___y_2880_ = v___y_2937_;
v___y_2881_ = v___y_2938_;
v_a_2882_ = v___x_2953_;
goto v___jp_2874_;
}
}
}
else
{
lean_object* v_a_2956_; 
v_a_2956_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2947_);
v___y_2895_ = v___y_2932_;
v___y_2896_ = v___y_2933_;
v___y_2897_ = v___y_2936_;
v___y_2898_ = v___x_2943_;
v___y_2899_ = v_a_2940_;
v___y_2900_ = v___y_2937_;
v___y_2901_ = v___y_2938_;
v_a_2902_ = v_a_2956_;
goto v___jp_2894_;
}
}
else
{
lean_object* v_a_2957_; 
lean_dec(v___y_2935_);
lean_dec_ref(v_cfg_2870_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
v_a_2957_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2944_);
v___y_2895_ = v___y_2932_;
v___y_2896_ = v___y_2933_;
v___y_2897_ = v___y_2936_;
v___y_2898_ = v___x_2943_;
v___y_2899_ = v_a_2940_;
v___y_2900_ = v___y_2937_;
v___y_2901_ = v___y_2938_;
v_a_2902_ = v_a_2957_;
goto v___jp_2894_;
}
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_io_get_num_heartbeats();
v___x_2959_ = l_Lean_MVarId_exfalso(v___y_2934_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_a_2960_);
lean_ctor_set(v___x_2961_, 1, v___y_2935_);
v___x_2962_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2862_, v_ctx_2863_, v_cfg_2870_, v___x_2961_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2962_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 1);
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
v___y_2905_ = v___y_2932_;
v___y_2906_ = v___y_2933_;
v___y_2907_ = v___x_2958_;
v___y_2908_ = v___y_2936_;
v___y_2909_ = v_a_2940_;
v___y_2910_ = v___y_2937_;
v___y_2911_ = v___y_2938_;
v_a_2912_ = v___x_2968_;
goto v___jp_2904_;
}
}
}
else
{
lean_object* v_a_2971_; 
v_a_2971_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2962_);
v___y_2922_ = v___y_2932_;
v___y_2923_ = v___y_2933_;
v___y_2924_ = v___x_2958_;
v___y_2925_ = v___y_2936_;
v___y_2926_ = v_a_2940_;
v___y_2927_ = v___y_2937_;
v___y_2928_ = v___y_2938_;
v_a_2929_ = v_a_2971_;
goto v___jp_2921_;
}
}
else
{
lean_object* v_a_2972_; 
lean_dec(v___y_2935_);
lean_dec_ref(v_cfg_2870_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
v_a_2972_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2972_);
lean_dec_ref(v___x_2959_);
v___y_2922_ = v___y_2932_;
v___y_2923_ = v___y_2933_;
v___y_2924_ = v___x_2958_;
v___y_2925_ = v___y_2936_;
v___y_2926_ = v_a_2940_;
v___y_2927_ = v___y_2937_;
v___y_2928_ = v___y_2938_;
v_a_2929_ = v_a_2972_;
goto v___jp_2921_;
}
}
}
v___jp_2973_:
{
if (v___y_2974_ == 0)
{
if (lean_obj_tag(v_goals_2864_) == 1)
{
lean_object* v_tail_2975_; 
v_tail_2975_ = lean_ctor_get(v_goals_2864_, 1);
lean_inc(v_tail_2975_);
if (lean_obj_tag(v_tail_2975_) == 0)
{
lean_object* v_toApplyRulesConfig_2976_; uint8_t v_exfalso_2977_; 
v_toApplyRulesConfig_2976_ = lean_ctor_get(v_cfg_2870_, 0);
lean_inc_ref(v_toApplyRulesConfig_2976_);
v_exfalso_2977_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2976_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2976_);
if (v_exfalso_2977_ == 1)
{
lean_object* v_options_2978_; uint8_t v_hasTrace_2979_; 
lean_dec_ref(v___x_2871_);
v_options_2978_ = lean_ctor_get(v_a_2867_, 2);
v_hasTrace_2979_ = lean_ctor_get_uint8(v_options_2978_, sizeof(void*)*1);
if (v_hasTrace_2979_ == 0)
{
lean_object* v_head_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2998_; 
v_head_2980_ = lean_ctor_get(v_goals_2864_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_goals_2864_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; 
v_unused_2999_ = lean_ctor_get(v_goals_2864_, 1);
lean_dec(v_unused_2999_);
v___x_2982_ = v_goals_2864_;
v_isShared_2983_ = v_isSharedCheck_2998_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_head_2980_);
lean_dec(v_goals_2864_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2998_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_MVarId_exfalso(v_head_2980_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref(v___x_2984_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_a_2985_);
v___x_2987_ = v___x_2982_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2985_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_tail_2975_);
v___x_2987_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; 
v___x_2988_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2862_, v_ctx_2863_, v_cfg_2870_, v___x_2987_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2988_;
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_del_object(v___x_2982_);
lean_dec_ref(v_cfg_2870_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
v_a_2990_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2984_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2984_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
else
{
lean_object* v_head_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3025_; 
v_head_3000_ = lean_ctor_get(v_goals_2864_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_goals_2864_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_goals_2864_, 1);
lean_dec(v_unused_3026_);
v___x_3002_ = v_goals_2864_;
v_isShared_3003_ = v_isSharedCheck_3025_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_head_3000_);
lean_dec(v_goals_2864_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3025_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v_inheritedTraceOptions_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_inheritedTraceOptions_3004_ = lean_ctor_get(v_a_2867_, 13);
v___x_3005_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3006_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3007_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3004_, v_options_2978_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = l_Lean_trace_profiler;
v___x_3010_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2978_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_MVarId_exfalso(v_head_3000_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___x_3011_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v_a_3012_);
v___x_3014_ = v___x_3002_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3012_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_tail_2975_);
v___x_3014_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2862_, v_ctx_2863_, v_cfg_2870_, v___x_3014_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_3015_;
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_del_object(v___x_3002_);
lean_dec_ref(v_cfg_2870_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
v_a_3017_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3011_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3011_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_del_object(v___x_3002_);
v___y_2932_ = v___x_3006_;
v___y_2933_ = v_exfalso_2977_;
v___y_2934_ = v_head_3000_;
v___y_2935_ = v_tail_2975_;
v___y_2936_ = v_options_2978_;
v___y_2937_ = v___x_3005_;
v___y_2938_ = v___x_3008_;
goto v___jp_2931_;
}
}
else
{
lean_del_object(v___x_3002_);
v___y_2932_ = v___x_3006_;
v___y_2933_ = v_exfalso_2977_;
v___y_2934_ = v_head_3000_;
v___y_2935_ = v_tail_2975_;
v___y_2936_ = v_options_2978_;
v___y_2937_ = v___x_3005_;
v___y_2938_ = v___x_3008_;
goto v___jp_2931_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2864_);
lean_dec_ref(v_cfg_2870_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
return v___x_2871_;
}
}
else
{
lean_dec_ref(v_goals_2864_);
lean_dec(v_tail_2975_);
lean_dec_ref(v_cfg_2870_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
return v___x_2871_;
}
}
else
{
lean_dec_ref(v_cfg_2870_);
lean_dec(v_goals_2864_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
return v___x_2871_;
}
}
else
{
lean_dec_ref(v_cfg_2870_);
lean_dec(v_goals_2864_);
lean_dec_ref(v_ctx_2863_);
lean_dec(v_lemmas_2862_);
return v___x_2871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3029_, lean_object* v_lemmas_3030_, lean_object* v_ctx_3031_, lean_object* v_goals_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3029_, v_lemmas_3030_, v_ctx_3031_, v_goals_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
if (lean_obj_tag(v_x_3039_) == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = l_List_reverse___redArg(v_x_3040_);
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
return v___x_3047_;
}
else
{
lean_object* v_head_3048_; lean_object* v_tail_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3072_; 
v_head_3048_ = lean_ctor_get(v_x_3039_, 0);
v_tail_3049_ = lean_ctor_get(v_x_3039_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_x_3039_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3051_ = v_x_3039_;
v_isShared_3052_ = v_isSharedCheck_3072_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_tail_3049_);
lean_inc(v_head_3048_);
lean_dec(v_x_3039_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3072_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_Expr_applySymm(v_head_3048_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v_x_3040_);
lean_ctor_set(v___x_3051_, 0, v_a_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3054_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_x_3040_);
v___x_3056_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
v_x_3039_ = v_tail_3049_;
v_x_3040_ = v___x_3056_;
goto _start;
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3071_; 
lean_del_object(v___x_3051_);
v_a_3059_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3061_ = v___x_3053_;
v_isShared_3062_ = v_isSharedCheck_3071_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3053_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3071_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
uint8_t v___y_3064_; uint8_t v___x_3069_; 
v___x_3069_ = l_Lean_Exception_isInterrupt(v_a_3059_);
if (v___x_3069_ == 0)
{
uint8_t v___x_3070_; 
lean_inc(v_a_3059_);
v___x_3070_ = l_Lean_Exception_isRuntime(v_a_3059_);
v___y_3064_ = v___x_3070_;
goto v___jp_3063_;
}
else
{
v___y_3064_ = v___x_3069_;
goto v___jp_3063_;
}
v___jp_3063_:
{
if (v___y_3064_ == 0)
{
lean_del_object(v___x_3061_);
lean_dec(v_a_3059_);
v_x_3039_ = v_tail_3049_;
goto _start;
}
else
{
lean_object* v___x_3067_; 
lean_dec(v_tail_3049_);
lean_dec(v_x_3040_);
if (v_isShared_3062_ == 0)
{
v___x_3067_ = v___x_3061_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3059_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3073_, lean_object* v_x_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3073_, v_x_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3081_, lean_object* v_hyps_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
if (v_symm_3081_ == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_hyps_3082_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_box(0);
lean_inc(v_hyps_3082_);
v___x_3090_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3082_, v___x_3089_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3099_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = l_List_appendTR___redArg(v_hyps_3082_, v_a_3091_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3095_);
v___x_3097_ = v___x_3093_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_dec(v_hyps_3082_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3100_, lean_object* v_hyps_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
uint8_t v_symm_boxed_3107_; lean_object* v_res_3108_; 
v_symm_boxed_3107_ = lean_unbox(v_symm_3100_);
v_res_3108_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3107_, v_hyps_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3109_, size_t v_sz_3110_, size_t v_i_3111_, lean_object* v_b_3112_){
_start:
{
uint8_t v___x_3114_; 
v___x_3114_ = lean_usize_dec_lt(v_i_3111_, v_sz_3110_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v_b_3112_);
return v___x_3115_;
}
else
{
lean_object* v_snd_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3134_; 
v_snd_3116_ = lean_ctor_get(v_b_3112_, 1);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_b_3112_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v_b_3112_, 0);
lean_dec(v_unused_3135_);
v___x_3118_ = v_b_3112_;
v_isShared_3119_ = v_isSharedCheck_3134_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_snd_3116_);
lean_dec(v_b_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3134_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v_a_3122_; lean_object* v_a_3129_; 
v___x_3120_ = lean_box(0);
v_a_3129_ = lean_array_uget_borrowed(v_as_3109_, v_i_3111_);
if (lean_obj_tag(v_a_3129_) == 0)
{
v_a_3122_ = v_snd_3116_;
goto v___jp_3121_;
}
else
{
lean_object* v_val_3130_; uint8_t v___x_3131_; 
v_val_3130_ = lean_ctor_get(v_a_3129_, 0);
v___x_3131_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_inc(v_val_3130_);
v___x_3132_ = l_Lean_LocalDecl_toExpr(v_val_3130_);
v___x_3133_ = lean_array_push(v_snd_3116_, v___x_3132_);
v_a_3122_ = v___x_3133_;
goto v___jp_3121_;
}
else
{
v_a_3122_ = v_snd_3116_;
goto v___jp_3121_;
}
}
v___jp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 1, v_a_3122_);
lean_ctor_set(v___x_3118_, 0, v___x_3120_);
v___x_3124_ = v___x_3118_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_a_3122_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
size_t v___x_3125_; size_t v___x_3126_; 
v___x_3125_ = ((size_t)1ULL);
v___x_3126_ = lean_usize_add(v_i_3111_, v___x_3125_);
v_i_3111_ = v___x_3126_;
v_b_3112_ = v___x_3124_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3136_, lean_object* v_sz_3137_, lean_object* v_i_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_){
_start:
{
size_t v_sz_boxed_3141_; size_t v_i_boxed_3142_; lean_object* v_res_3143_; 
v_sz_boxed_3141_ = lean_unbox_usize(v_sz_3137_);
lean_dec(v_sz_3137_);
v_i_boxed_3142_ = lean_unbox_usize(v_i_3138_);
lean_dec(v_i_3138_);
v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3136_, v_sz_boxed_3141_, v_i_boxed_3142_, v_b_3139_);
lean_dec_ref(v_as_3136_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3144_, size_t v_sz_3145_, size_t v_i_3146_, lean_object* v_b_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_usize_dec_lt(v_i_3146_, v_sz_3145_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_b_3147_);
return v___x_3156_;
}
else
{
lean_object* v_snd_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3175_; 
v_snd_3157_ = lean_ctor_get(v_b_3147_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_b_3147_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v_b_3147_, 0);
lean_dec(v_unused_3176_);
v___x_3159_ = v_b_3147_;
v_isShared_3160_ = v_isSharedCheck_3175_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_snd_3157_);
lean_dec(v_b_3147_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3175_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v_a_3163_; lean_object* v_a_3170_; 
v___x_3161_ = lean_box(0);
v_a_3170_ = lean_array_uget_borrowed(v_as_3144_, v_i_3146_);
if (lean_obj_tag(v_a_3170_) == 0)
{
v_a_3163_ = v_snd_3157_;
goto v___jp_3162_;
}
else
{
lean_object* v_val_3171_; uint8_t v___x_3172_; 
v_val_3171_ = lean_ctor_get(v_a_3170_, 0);
v___x_3172_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_inc(v_val_3171_);
v___x_3173_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3174_ = lean_array_push(v_snd_3157_, v___x_3173_);
v_a_3163_ = v___x_3174_;
goto v___jp_3162_;
}
else
{
v_a_3163_ = v_snd_3157_;
goto v___jp_3162_;
}
}
v___jp_3162_:
{
lean_object* v___x_3165_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 1, v_a_3163_);
lean_ctor_set(v___x_3159_, 0, v___x_3161_);
v___x_3165_ = v___x_3159_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_a_3163_);
v___x_3165_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = ((size_t)1ULL);
v___x_3167_ = lean_usize_add(v_i_3146_, v___x_3166_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3144_, v_sz_3145_, v___x_3167_, v___x_3165_);
return v___x_3168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3177_, lean_object* v_sz_3178_, lean_object* v_i_3179_, lean_object* v_b_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
size_t v_sz_boxed_3188_; size_t v_i_boxed_3189_; lean_object* v_res_3190_; 
v_sz_boxed_3188_ = lean_unbox_usize(v_sz_3178_);
lean_dec(v_sz_3178_);
v_i_boxed_3189_ = lean_unbox_usize(v_i_3179_);
lean_dec(v_i_3179_);
v_res_3190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3177_, v_sz_boxed_3188_, v_i_boxed_3189_, v_b_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec_ref(v_as_3177_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3191_, size_t v_sz_3192_, size_t v_i_3193_, lean_object* v_b_3194_){
_start:
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_usize_dec_lt(v_i_3193_, v_sz_3192_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v_b_3194_);
return v___x_3197_;
}
else
{
lean_object* v_snd_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3216_; 
v_snd_3198_ = lean_ctor_get(v_b_3194_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_b_3194_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v_b_3194_, 0);
lean_dec(v_unused_3217_);
v___x_3200_ = v_b_3194_;
v_isShared_3201_ = v_isSharedCheck_3216_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_snd_3198_);
lean_dec(v_b_3194_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3216_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v_a_3204_; lean_object* v_a_3211_; 
v___x_3202_ = lean_box(0);
v_a_3211_ = lean_array_uget_borrowed(v_as_3191_, v_i_3193_);
if (lean_obj_tag(v_a_3211_) == 0)
{
v_a_3204_ = v_snd_3198_;
goto v___jp_3203_;
}
else
{
lean_object* v_val_3212_; uint8_t v___x_3213_; 
v_val_3212_ = lean_ctor_get(v_a_3211_, 0);
v___x_3213_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_inc(v_val_3212_);
v___x_3214_ = l_Lean_LocalDecl_toExpr(v_val_3212_);
v___x_3215_ = lean_array_push(v_snd_3198_, v___x_3214_);
v_a_3204_ = v___x_3215_;
goto v___jp_3203_;
}
else
{
v_a_3204_ = v_snd_3198_;
goto v___jp_3203_;
}
}
v___jp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 1, v_a_3204_);
lean_ctor_set(v___x_3200_, 0, v___x_3202_);
v___x_3206_ = v___x_3200_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_a_3204_);
v___x_3206_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
size_t v___x_3207_; size_t v___x_3208_; 
v___x_3207_ = ((size_t)1ULL);
v___x_3208_ = lean_usize_add(v_i_3193_, v___x_3207_);
v_i_3193_ = v___x_3208_;
v_b_3194_ = v___x_3206_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3218_, lean_object* v_sz_3219_, lean_object* v_i_3220_, lean_object* v_b_3221_, lean_object* v___y_3222_){
_start:
{
size_t v_sz_boxed_3223_; size_t v_i_boxed_3224_; lean_object* v_res_3225_; 
v_sz_boxed_3223_ = lean_unbox_usize(v_sz_3219_);
lean_dec(v_sz_3219_);
v_i_boxed_3224_ = lean_unbox_usize(v_i_3220_);
lean_dec(v_i_3220_);
v_res_3225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3218_, v_sz_boxed_3223_, v_i_boxed_3224_, v_b_3221_);
lean_dec_ref(v_as_3218_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3226_, size_t v_sz_3227_, size_t v_i_3228_, lean_object* v_b_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
uint8_t v___x_3237_; 
v___x_3237_ = lean_usize_dec_lt(v_i_3228_, v_sz_3227_);
if (v___x_3237_ == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_b_3229_);
return v___x_3238_;
}
else
{
lean_object* v_snd_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3257_; 
v_snd_3239_ = lean_ctor_get(v_b_3229_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_b_3229_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v_b_3229_, 0);
lean_dec(v_unused_3258_);
v___x_3241_ = v_b_3229_;
v_isShared_3242_ = v_isSharedCheck_3257_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_snd_3239_);
lean_dec(v_b_3229_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3257_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v_a_3245_; lean_object* v_a_3252_; 
v___x_3243_ = lean_box(0);
v_a_3252_ = lean_array_uget_borrowed(v_as_3226_, v_i_3228_);
if (lean_obj_tag(v_a_3252_) == 0)
{
v_a_3245_ = v_snd_3239_;
goto v___jp_3244_;
}
else
{
lean_object* v_val_3253_; uint8_t v___x_3254_; 
v_val_3253_ = lean_ctor_get(v_a_3252_, 0);
v___x_3254_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_inc(v_val_3253_);
v___x_3255_ = l_Lean_LocalDecl_toExpr(v_val_3253_);
v___x_3256_ = lean_array_push(v_snd_3239_, v___x_3255_);
v_a_3245_ = v___x_3256_;
goto v___jp_3244_;
}
else
{
v_a_3245_ = v_snd_3239_;
goto v___jp_3244_;
}
}
v___jp_3244_:
{
lean_object* v___x_3247_; 
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v_a_3245_);
lean_ctor_set(v___x_3241_, 0, v___x_3243_);
v___x_3247_ = v___x_3241_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_a_3245_);
v___x_3247_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
size_t v___x_3248_; size_t v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = ((size_t)1ULL);
v___x_3249_ = lean_usize_add(v_i_3228_, v___x_3248_);
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3226_, v_sz_3227_, v___x_3249_, v___x_3247_);
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3259_, lean_object* v_sz_3260_, lean_object* v_i_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
size_t v_sz_boxed_3270_; size_t v_i_boxed_3271_; lean_object* v_res_3272_; 
v_sz_boxed_3270_ = lean_unbox_usize(v_sz_3260_);
lean_dec(v_sz_3260_);
v_i_boxed_3271_ = lean_unbox_usize(v_i_3261_);
lean_dec(v_i_3261_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3259_, v_sz_boxed_3270_, v_i_boxed_3271_, v_b_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v_as_3259_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3273_, lean_object* v_n_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
if (lean_obj_tag(v_n_3274_) == 0)
{
lean_object* v_cs_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3317_; 
v_cs_3283_ = lean_ctor_get(v_n_3274_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_n_3274_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3285_ = v_n_3274_;
v_isShared_3286_ = v_isSharedCheck_3317_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_cs_3283_);
lean_dec(v_n_3274_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3317_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; size_t v_sz_3289_; size_t v___x_3290_; lean_object* v___x_3291_; 
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
lean_ctor_set(v___x_3288_, 1, v_b_3275_);
v_sz_3289_ = lean_array_size(v_cs_3283_);
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3273_, v_cs_3283_, v_sz_3289_, v___x_3290_, v___x_3288_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec_ref(v_cs_3283_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3308_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3308_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3308_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v_fst_3296_; 
v_fst_3296_ = lean_ctor_get(v_a_3292_, 0);
if (lean_obj_tag(v_fst_3296_) == 0)
{
lean_object* v_snd_3297_; lean_object* v___x_3299_; 
v_snd_3297_ = lean_ctor_get(v_a_3292_, 1);
lean_inc(v_snd_3297_);
lean_dec(v_a_3292_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 1);
lean_ctor_set(v___x_3285_, 0, v_snd_3297_);
v___x_3299_ = v___x_3285_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_snd_3297_);
v___x_3299_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3301_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v___x_3299_);
v___x_3301_ = v___x_3294_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
else
{
lean_object* v_val_3304_; lean_object* v___x_3306_; 
lean_inc_ref(v_fst_3296_);
lean_dec(v_a_3292_);
lean_del_object(v___x_3285_);
v_val_3304_ = lean_ctor_get(v_fst_3296_, 0);
lean_inc(v_val_3304_);
lean_dec_ref(v_fst_3296_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v_val_3304_);
v___x_3306_ = v___x_3294_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_val_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_del_object(v___x_3285_);
v_a_3309_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3291_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3291_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
else
{
lean_object* v_vs_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3352_; 
v_vs_3318_ = lean_ctor_get(v_n_3274_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_n_3274_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3320_ = v_n_3274_;
v_isShared_3321_ = v_isSharedCheck_3352_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_vs_3318_);
lean_dec(v_n_3274_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3352_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; size_t v_sz_3324_; size_t v___x_3325_; lean_object* v___x_3326_; 
v___x_3322_ = lean_box(0);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3322_);
lean_ctor_set(v___x_3323_, 1, v_b_3275_);
v_sz_3324_ = lean_array_size(v_vs_3318_);
v___x_3325_ = ((size_t)0ULL);
v___x_3326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3318_, v_sz_3324_, v___x_3325_, v___x_3323_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec_ref(v_vs_3318_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3343_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3343_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3343_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v_fst_3331_; 
v_fst_3331_ = lean_ctor_get(v_a_3327_, 0);
if (lean_obj_tag(v_fst_3331_) == 0)
{
lean_object* v_snd_3332_; lean_object* v___x_3334_; 
v_snd_3332_ = lean_ctor_get(v_a_3327_, 1);
lean_inc(v_snd_3332_);
lean_dec(v_a_3327_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_snd_3332_);
v___x_3334_ = v___x_3320_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_snd_3332_);
v___x_3334_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3336_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3334_);
v___x_3336_ = v___x_3329_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
else
{
lean_object* v_val_3339_; lean_object* v___x_3341_; 
lean_inc_ref(v_fst_3331_);
lean_dec(v_a_3327_);
lean_del_object(v___x_3320_);
v_val_3339_ = lean_ctor_get(v_fst_3331_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v_fst_3331_);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v_val_3339_);
v___x_3341_ = v___x_3329_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_val_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_del_object(v___x_3320_);
v_a_3344_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3326_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3326_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3353_, lean_object* v_as_3354_, size_t v_sz_3355_, size_t v_i_3356_, lean_object* v_b_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3356_, v_sz_3355_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3357_);
return v___x_3366_;
}
else
{
lean_object* v_snd_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3401_; 
v_snd_3367_ = lean_ctor_get(v_b_3357_, 1);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_b_3357_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v_b_3357_, 0);
lean_dec(v_unused_3402_);
v___x_3369_ = v_b_3357_;
v_isShared_3370_ = v_isSharedCheck_3401_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snd_3367_);
lean_dec(v_b_3357_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3401_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v_a_3371_; lean_object* v___x_3372_; 
v_a_3371_ = lean_array_uget_borrowed(v_as_3354_, v_i_3356_);
lean_inc(v_snd_3367_);
lean_inc(v_a_3371_);
v___x_3372_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3353_, v_a_3371_, v_snd_3367_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3392_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3392_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3392_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
if (lean_obj_tag(v_a_3373_) == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v_a_3373_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3377_);
v___x_3379_ = v___x_3369_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_snd_3367_);
v___x_3379_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3381_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3379_);
v___x_3381_ = v___x_3375_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
lean_del_object(v___x_3375_);
lean_dec(v_snd_3367_);
v_a_3384_ = lean_ctor_get(v_a_3373_, 0);
lean_inc(v_a_3384_);
lean_dec_ref(v_a_3373_);
v___x_3385_ = lean_box(0);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 1, v_a_3384_);
lean_ctor_set(v___x_3369_, 0, v___x_3385_);
v___x_3387_ = v___x_3369_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_a_3384_);
v___x_3387_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
size_t v___x_3388_; size_t v___x_3389_; 
v___x_3388_ = ((size_t)1ULL);
v___x_3389_ = lean_usize_add(v_i_3356_, v___x_3388_);
v_i_3356_ = v___x_3389_;
v_b_3357_ = v___x_3387_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_del_object(v___x_3369_);
lean_dec(v_snd_3367_);
v_a_3393_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3372_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3372_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3403_, lean_object* v_as_3404_, lean_object* v_sz_3405_, lean_object* v_i_3406_, lean_object* v_b_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
size_t v_sz_boxed_3415_; size_t v_i_boxed_3416_; lean_object* v_res_3417_; 
v_sz_boxed_3415_ = lean_unbox_usize(v_sz_3405_);
lean_dec(v_sz_3405_);
v_i_boxed_3416_ = lean_unbox_usize(v_i_3406_);
lean_dec(v_i_3406_);
v_res_3417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3403_, v_as_3404_, v_sz_boxed_3415_, v_i_boxed_3416_, v_b_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v_as_3404_);
lean_dec_ref(v_init_3403_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3418_, lean_object* v_n_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3418_, v_n_3419_, v_b_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v_init_3418_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3429_, lean_object* v_init_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_root_3438_; lean_object* v_tail_3439_; lean_object* v___x_3440_; 
v_root_3438_ = lean_ctor_get(v_t_3429_, 0);
lean_inc_ref(v_root_3438_);
v_tail_3439_ = lean_ctor_get(v_t_3429_, 1);
lean_inc_ref(v_tail_3439_);
lean_dec_ref(v_t_3429_);
lean_inc_ref(v_init_3430_);
v___x_3440_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3430_, v_root_3438_, v_init_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec_ref(v_init_3430_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3477_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3477_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3477_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
if (lean_obj_tag(v_a_3441_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; 
lean_dec_ref(v_tail_3439_);
v_a_3445_ = lean_ctor_get(v_a_3441_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v_a_3441_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v_a_3445_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; size_t v_sz_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
lean_del_object(v___x_3443_);
v_a_3449_ = lean_ctor_get(v_a_3441_, 0);
lean_inc(v_a_3449_);
lean_dec_ref(v_a_3441_);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v_a_3449_);
v_sz_3452_ = lean_array_size(v_tail_3439_);
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3439_, v_sz_3452_, v___x_3453_, v___x_3451_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec_ref(v_tail_3439_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3468_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3468_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3468_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_fst_3459_; 
v_fst_3459_ = lean_ctor_get(v_a_3455_, 0);
if (lean_obj_tag(v_fst_3459_) == 0)
{
lean_object* v_snd_3460_; lean_object* v___x_3462_; 
v_snd_3460_ = lean_ctor_get(v_a_3455_, 1);
lean_inc(v_snd_3460_);
lean_dec(v_a_3455_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v_snd_3460_);
v___x_3462_ = v___x_3457_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_snd_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
else
{
lean_object* v_val_3464_; lean_object* v___x_3466_; 
lean_inc_ref(v_fst_3459_);
lean_dec(v_a_3455_);
v_val_3464_ = lean_ctor_get(v_fst_3459_, 0);
lean_inc(v_val_3464_);
lean_dec_ref(v_fst_3459_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v_val_3464_);
v___x_3466_ = v___x_3457_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_val_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
v_a_3469_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3454_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3454_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_tail_3439_);
v_a_3478_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3440_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3440_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3486_, lean_object* v_init_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3486_, v_init_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_lctx_3505_; lean_object* v_decls_3506_; lean_object* v_hs_3507_; lean_object* v___x_3508_; 
v_lctx_3505_ = lean_ctor_get(v___y_3500_, 2);
v_decls_3506_ = lean_ctor_get(v_lctx_3505_, 1);
v_hs_3507_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
lean_inc_ref(v_decls_3506_);
v___x_3508_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3506_, v_hs_3507_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3517_, lean_object* v_cfg_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
if (v_only_3517_ == 0)
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_toApplyRulesConfig_3527_; lean_object* v_a_3528_; uint8_t v_symm_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_toApplyRulesConfig_3527_ = lean_ctor_get(v_cfg_3518_, 0);
v_a_3528_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3528_);
lean_dec_ref(v___x_3526_);
v_symm_3529_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3527_, sizeof(void*)*2 + 1);
v___x_3530_ = lean_array_to_list(v_a_3528_);
v___x_3531_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3529_, v___x_3530_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
return v___x_3531_;
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3526_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3526_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_box(0);
v___x_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3542_, lean_object* v_cfg_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
uint8_t v_only_boxed_3551_; lean_object* v_res_3552_; 
v_only_boxed_3551_ = lean_unbox(v_only_3542_);
v_res_3552_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3551_, v_cfg_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v_cfg_3543_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3553_, lean_object* v_lemmas_3554_, uint8_t v_only_3555_, lean_object* v_g_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_toApplyRulesConfig_3562_; uint8_t v_intro_3563_; uint8_t v_constructor_3564_; uint8_t v_suggestions_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3578_; 
v_toApplyRulesConfig_3562_ = lean_ctor_get(v_cfg_3553_, 0);
v_intro_3563_ = lean_ctor_get_uint8(v_cfg_3553_, sizeof(void*)*1 + 1);
v_constructor_3564_ = lean_ctor_get_uint8(v_cfg_3553_, sizeof(void*)*1 + 2);
v_suggestions_3565_ = lean_ctor_get_uint8(v_cfg_3553_, sizeof(void*)*1 + 3);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_cfg_3553_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3567_ = v_cfg_3553_;
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_toApplyRulesConfig_3562_);
lean_dec(v_cfg_3553_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3578_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v_ctx_3570_; uint8_t v___x_3571_; lean_object* v___x_3573_; 
v___x_3569_ = lean_box(v_only_3555_);
v_ctx_3570_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3570_, 0, v___x_3569_);
v___x_3571_ = 0;
if (v_isShared_3568_ == 0)
{
v___x_3573_ = v___x_3567_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_toApplyRulesConfig_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*1 + 1, v_intro_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*1 + 2, v_constructor_3564_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*1 + 3, v_suggestions_3565_);
v___x_3573_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
lean_ctor_set_uint8(v___x_3573_, sizeof(void*)*1, v___x_3571_);
v___x_3574_ = lean_box(0);
v___x_3575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3575_, 0, v_g_3556_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3573_, v_lemmas_3554_, v_ctx_3570_, v___x_3575_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
return v___x_3576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3579_, lean_object* v_lemmas_3580_, lean_object* v_only_3581_, lean_object* v_g_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
uint8_t v_only_boxed_3588_; lean_object* v_res_3589_; 
v_only_boxed_3588_ = lean_unbox(v_only_3581_);
v_res_3589_ = l_Lean_MVarId_applyRules(v_cfg_3579_, v_lemmas_3580_, v_only_boxed_3588_, v_g_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3590_, size_t v_sz_3591_, size_t v_i_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3590_, v_sz_3591_, v_i_3592_, v_b_3593_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3602_, lean_object* v_sz_3603_, lean_object* v_i_3604_, lean_object* v_b_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
size_t v_sz_boxed_3613_; size_t v_i_boxed_3614_; lean_object* v_res_3615_; 
v_sz_boxed_3613_ = lean_unbox_usize(v_sz_3603_);
lean_dec(v_sz_3603_);
v_i_boxed_3614_ = lean_unbox_usize(v_i_3604_);
lean_dec(v_i_3604_);
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3602_, v_sz_boxed_3613_, v_i_boxed_3614_, v_b_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_as_3602_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3616_, size_t v_sz_3617_, size_t v_i_3618_, lean_object* v_b_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3616_, v_sz_3617_, v_i_3618_, v_b_3619_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3628_, lean_object* v_sz_3629_, lean_object* v_i_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3629_);
lean_dec(v_sz_3629_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3628_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_as_3628_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; 
v___x_3650_ = lean_box(0);
v___x_3651_ = 1;
v___x_3652_ = l_Lean_Elab_Term_elabTerm(v_t_3642_, v___x_3650_, v___x_3651_, v___x_3651_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_a_3657_);
lean_dec_ref(v_a_3656_);
lean_dec(v_a_3655_);
lean_dec_ref(v_a_3654_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_ref_3667_; uint8_t v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_ref_3667_ = lean_ctor_get(v___y_3664_, 5);
v___x_3668_ = 0;
v___x_3669_ = l_Lean_SourceInfo_fromRef(v_ref_3667_, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3677_, lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
uint8_t v___x_3679_; 
v___x_3679_ = 0;
return v___x_3679_;
}
else
{
lean_object* v_head_3680_; lean_object* v_tail_3681_; uint8_t v___x_3682_; 
v_head_3680_ = lean_ctor_get(v_x_3678_, 0);
v_tail_3681_ = lean_ctor_get(v_x_3678_, 1);
v___x_3682_ = lean_expr_eqv(v_a_3677_, v_head_3680_);
if (v___x_3682_ == 0)
{
v_x_3678_ = v_tail_3681_;
goto _start;
}
else
{
return v___x_3682_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3684_, lean_object* v_x_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3684_, v_x_3685_);
lean_dec(v_x_3685_);
lean_dec_ref(v_a_3684_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3688_, lean_object* v_x_3689_){
_start:
{
uint8_t v___x_3690_; 
v___x_3690_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3689_, v_ys_3688_);
if (v___x_3690_ == 0)
{
uint8_t v___x_3691_; 
v___x_3691_ = 1;
return v___x_3691_;
}
else
{
uint8_t v___x_3692_; 
v___x_3692_ = 0;
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3693_, lean_object* v_x_3694_){
_start:
{
uint8_t v_res_3695_; lean_object* v_r_3696_; 
v_res_3695_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3693_, v_x_3694_);
lean_dec_ref(v_x_3694_);
lean_dec(v_ys_3693_);
v_r_3696_ = lean_box(v_res_3695_);
return v_r_3696_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3697_, lean_object* v_ys_3698_){
_start:
{
lean_object* v___f_3699_; lean_object* v___x_3700_; 
v___f_3699_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3699_, 0, v_ys_3698_);
v___x_3700_ = l_List_filter___redArg(v___f_3699_, v_xs_3697_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3701_, lean_object* v_x_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
if (lean_obj_tag(v_x_3701_) == 0)
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = l_List_reverse___redArg(v_x_3702_);
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
else
{
lean_object* v_head_3712_; lean_object* v_tail_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3731_; 
v_head_3712_ = lean_ctor_get(v_x_3701_, 0);
v_tail_3713_ = lean_ctor_get(v_x_3701_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_x_3701_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3715_ = v_x_3701_;
v_isShared_3716_ = v_isSharedCheck_3731_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_tail_3713_);
lean_inc(v_head_3712_);
lean_dec(v_x_3701_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3731_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; 
v___x_3717_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3712_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 1, v_x_3702_);
lean_ctor_set(v___x_3715_, 0, v_a_3718_);
v___x_3720_ = v___x_3715_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3718_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_x_3702_);
v___x_3720_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
v_x_3701_ = v_tail_3713_;
v_x_3702_ = v___x_3720_;
goto _start;
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3715_);
lean_dec(v_tail_3713_);
lean_dec(v_x_3702_);
v_a_3723_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3717_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3717_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3732_, lean_object* v_x_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3732_, v_x_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3742_, uint8_t v_noDefaults_3743_, uint8_t v_star_3744_, lean_object* v_cfg_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
if (v_noDefaults_3743_ == 0)
{
goto v___jp_3753_;
}
else
{
if (v_star_3744_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
lean_dec(v_remove_3742_);
v___x_3772_ = lean_box(0);
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
else
{
goto v___jp_3753_;
}
}
v___jp_3753_:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref(v___x_3754_);
v___x_3756_ = lean_box(0);
v___x_3757_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3742_, v___x_3756_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_toApplyRulesConfig_3758_; lean_object* v_a_3759_; uint8_t v_symm_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_toApplyRulesConfig_3758_ = lean_ctor_get(v_cfg_3745_, 0);
v_a_3759_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3757_);
v_symm_3760_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3758_, sizeof(void*)*2 + 1);
v___x_3761_ = lean_array_to_list(v_a_3755_);
v___x_3762_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3761_, v_a_3759_);
v___x_3763_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3760_, v___x_3762_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3763_;
}
else
{
lean_dec(v_a_3755_);
return v___x_3757_;
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec(v_remove_3742_);
v_a_3764_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3754_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3754_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3774_, lean_object* v_noDefaults_3775_, lean_object* v_star_3776_, lean_object* v_cfg_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
uint8_t v_noDefaults_boxed_3785_; uint8_t v_star_boxed_3786_; lean_object* v_res_3787_; 
v_noDefaults_boxed_3785_ = lean_unbox(v_noDefaults_3775_);
v_star_boxed_3786_ = lean_unbox(v_star_3776_);
v_res_3787_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3774_, v_noDefaults_boxed_3785_, v_star_boxed_3786_, v_cfg_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v_cfg_3777_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3788_, size_t v_i_3789_, size_t v_stop_3790_, lean_object* v_b_3791_){
_start:
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_eq(v_i_3789_, v_stop_3790_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; size_t v___x_3795_; size_t v___x_3796_; 
v___x_3793_ = lean_array_uget_borrowed(v_as_3788_, v_i_3789_);
v___x_3794_ = l_Array_append___redArg(v_b_3791_, v___x_3793_);
v___x_3795_ = ((size_t)1ULL);
v___x_3796_ = lean_usize_add(v_i_3789_, v___x_3795_);
v_i_3789_ = v___x_3796_;
v_b_3791_ = v___x_3794_;
goto _start;
}
else
{
return v_b_3791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3798_, lean_object* v_i_3799_, lean_object* v_stop_3800_, lean_object* v_b_3801_){
_start:
{
size_t v_i_boxed_3802_; size_t v_stop_boxed_3803_; lean_object* v_res_3804_; 
v_i_boxed_3802_ = lean_unbox_usize(v_i_3799_);
lean_dec(v_i_3799_);
v_stop_boxed_3803_ = lean_unbox_usize(v_stop_3800_);
lean_dec(v_stop_3800_);
v_res_3804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3798_, v_i_boxed_3802_, v_stop_boxed_3803_, v_b_3801_);
lean_dec_ref(v_as_3798_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
if (lean_obj_tag(v_a_3805_) == 0)
{
lean_object* v___x_3807_; 
v___x_3807_ = l_List_reverse___redArg(v_a_3806_);
return v___x_3807_;
}
else
{
lean_object* v_head_3808_; lean_object* v_tail_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3818_; 
v_head_3808_ = lean_ctor_get(v_a_3805_, 0);
v_tail_3809_ = lean_ctor_get(v_a_3805_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3805_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3811_ = v_a_3805_;
v_isShared_3812_ = v_isSharedCheck_3818_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_tail_3809_);
lean_inc(v_head_3808_);
lean_dec(v_a_3805_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3818_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3813_, 0, v_head_3808_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v_a_3806_);
lean_ctor_set(v___x_3811_, 0, v___x_3813_);
v___x_3815_ = v___x_3811_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_a_3806_);
v___x_3815_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
v_a_3805_ = v_tail_3809_;
v_a_3806_ = v___x_3815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3819_, size_t v_i_3820_, lean_object* v_bs_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_usize_dec_lt(v_i_3820_, v_sz_3819_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_bs_3821_);
return v___x_3826_;
}
else
{
lean_object* v_v_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_v_3827_ = lean_array_uget_borrowed(v_bs_3821_, v_i_3820_);
v___x_3828_ = l_Lean_Syntax_getId(v_v_3827_);
v___x_3829_ = l_Lean_labelled(v___x_3828_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; lean_object* v_bs_x27_3832_; size_t v___x_3833_; size_t v___x_3834_; lean_object* v___x_3835_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = lean_unsigned_to_nat(0u);
v_bs_x27_3832_ = lean_array_uset(v_bs_3821_, v_i_3820_, v___x_3831_);
v___x_3833_ = ((size_t)1ULL);
v___x_3834_ = lean_usize_add(v_i_3820_, v___x_3833_);
v___x_3835_ = lean_array_uset(v_bs_x27_3832_, v_i_3820_, v_a_3830_);
v_i_3820_ = v___x_3834_;
v_bs_3821_ = v___x_3835_;
goto _start;
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_bs_3821_);
v_a_3837_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3829_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3829_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3845_, lean_object* v_i_3846_, lean_object* v_bs_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3845_);
lean_dec(v_sz_3845_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3846_);
lean_dec(v_i_3846_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3851_, v_i_boxed_3852_, v_bs_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3854_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
if (lean_obj_tag(v_a_3872_) == 0)
{
lean_object* v___x_3874_; 
v___x_3874_ = l_List_reverse___redArg(v_a_3873_);
return v___x_3874_;
}
else
{
lean_object* v_head_3875_; lean_object* v_tail_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3885_; 
v_head_3875_ = lean_ctor_get(v_a_3872_, 0);
v_tail_3876_ = lean_ctor_get(v_a_3872_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_a_3872_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3878_ = v_a_3872_;
v_isShared_3879_ = v_isSharedCheck_3885_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_tail_3876_);
lean_inc(v_head_3875_);
lean_dec(v_a_3872_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3885_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___f_3880_; lean_object* v___x_3882_; 
v___f_3880_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3880_, 0, v_head_3875_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 1, v_a_3873_);
lean_ctor_set(v___x_3878_, 0, v___f_3880_);
v___x_3882_ = v___x_3878_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___f_3880_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_a_3873_);
v___x_3882_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
v_a_3872_ = v_tail_3876_;
v_a_3873_ = v___x_3882_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3888_ = l_Lean_stringToMessageData(v___x_3887_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3891_ = l_String_toRawSubstring_x27(v___x_3890_);
return v___x_3891_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3896_ = l_String_toRawSubstring_x27(v___x_3895_);
return v___x_3896_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3901_ = l_String_toRawSubstring_x27(v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3906_ = l_String_toRawSubstring_x27(v___x_3905_);
return v___x_3906_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3937_ = l_Lean_stringToMessageData(v___x_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3938_, uint8_t v_star_3939_, lean_object* v_add_3940_, lean_object* v_remove_3941_, lean_object* v_use_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___f_3973_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; 
v___x_3971_ = lean_box(v_noDefaults_3938_);
v___x_3972_ = lean_box(v_star_3939_);
lean_inc(v_remove_3941_);
v___f_3973_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3973_, 0, v_remove_3941_);
lean_closure_set(v___f_3973_, 1, v___x_3971_);
lean_closure_set(v___f_3973_, 2, v___x_3972_);
if (v_star_3939_ == 0)
{
v___y_3990_ = v_a_3943_;
v___y_3991_ = v_a_3944_;
v___y_3992_ = v_a_3945_;
v___y_3993_ = v_a_3946_;
goto v___jp_3989_;
}
else
{
if (v_noDefaults_3938_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec_ref(v___f_3973_);
lean_dec_ref(v_use_3942_);
lean_dec(v_remove_3941_);
lean_dec(v_add_3940_);
v___x_4052_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4053_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4052_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
else
{
v___y_3990_ = v_a_3943_;
v___y_3991_ = v_a_3944_;
v___y_3992_ = v_a_3945_;
v___y_3993_ = v_a_3946_;
goto v___jp_3989_;
}
}
v___jp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___y_3949_);
lean_ctor_set(v___x_3951_, 1, v___y_3950_);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
v___jp_3953_:
{
uint8_t v___x_3960_; 
v___x_3960_ = l_List_isEmpty___redArg(v_remove_3941_);
lean_dec(v_remove_3941_);
if (v___x_3960_ == 0)
{
if (v_noDefaults_3938_ == 0)
{
v___y_3949_ = v___y_3959_;
v___y_3950_ = v___y_3958_;
goto v___jp_3948_;
}
else
{
if (v_star_3939_ == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
v___x_3961_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3962_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3961_, v___y_3957_, v___y_3956_, v___y_3954_, v___y_3955_);
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
else
{
v___y_3949_ = v___y_3959_;
v___y_3950_ = v___y_3958_;
goto v___jp_3948_;
}
}
}
else
{
v___y_3949_ = v___y_3959_;
v___y_3950_ = v___y_3958_;
goto v___jp_3948_;
}
}
v___jp_3974_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = lean_array_to_list(v___y_3981_);
lean_inc(v___y_3977_);
v___x_3983_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3982_, v___y_3977_);
if (v_noDefaults_3938_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3940_, v___y_3977_);
v___x_3985_ = l_List_appendTR___redArg(v___x_3984_, v___x_3983_);
v___x_3986_ = l_List_appendTR___redArg(v___x_3985_, v___y_3980_);
v___y_3954_ = v___y_3975_;
v___y_3955_ = v___y_3976_;
v___y_3956_ = v___y_3979_;
v___y_3957_ = v___y_3978_;
v___y_3958_ = v___f_3973_;
v___y_3959_ = v___x_3986_;
goto v___jp_3953_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_dec(v___y_3980_);
v___x_3987_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3940_, v___y_3977_);
v___x_3988_ = l_List_appendTR___redArg(v___x_3987_, v___x_3983_);
v___y_3954_ = v___y_3975_;
v___y_3955_ = v___y_3976_;
v___y_3956_ = v___y_3979_;
v___y_3957_ = v___y_3978_;
v___y_3958_ = v___f_3973_;
v___y_3959_ = v___x_3988_;
goto v___jp_3953_;
}
}
v___jp_3989_:
{
lean_object* v_ref_3994_; lean_object* v_quotContext_3995_; lean_object* v_currMacroScope_3996_; lean_object* v___x_3997_; lean_object* v_a_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v_a_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v_a_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; size_t v_sz_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v_ref_3994_ = lean_ctor_get(v___y_3992_, 5);
v_quotContext_3995_ = lean_ctor_get(v___y_3992_, 10);
v_currMacroScope_3996_ = lean_ctor_get(v___y_3992_, 11);
v___x_3997_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref(v___x_3997_);
v___x_3999_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4000_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v___x_4002_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3996_, 2);
lean_inc_n(v_quotContext_3995_, 2);
v___x_4003_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4002_, v_currMacroScope_3996_);
v___x_4004_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4005_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_4005_);
v___x_4007_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4008_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4007_, v_currMacroScope_3996_);
v___x_4009_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4010_ = lean_array_size(v_use_3942_);
v___x_4011_ = ((size_t)0ULL);
v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4010_, v___x_4011_, v_use_3942_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref(v___x_4012_);
v___x_4014_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3996_, 2);
lean_inc_n(v_quotContext_3995_, 2);
v___x_4015_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4014_, v_currMacroScope_3996_);
v___x_4016_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4017_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4018_ = l_Lean_addMacroScope(v_quotContext_3995_, v___x_4017_, v_currMacroScope_3996_);
v___x_4019_ = 0;
v___x_4020_ = l_Lean_SourceInfo_fromRef(v_ref_3994_, v___x_4019_);
v___x_4021_ = lean_box(0);
v___x_4022_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4023_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4020_);
lean_ctor_set(v___x_4023_, 1, v___x_3999_);
lean_ctor_set(v___x_4023_, 2, v___x_4003_);
lean_ctor_set(v___x_4023_, 3, v___x_4022_);
v___x_4024_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4025_, 0, v_a_3998_);
lean_ctor_set(v___x_4025_, 1, v___x_4004_);
lean_ctor_set(v___x_4025_, 2, v___x_4008_);
lean_ctor_set(v___x_4025_, 3, v___x_4024_);
v___x_4026_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4027_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4027_, 0, v_a_4001_);
lean_ctor_set(v___x_4027_, 1, v___x_4009_);
lean_ctor_set(v___x_4027_, 2, v___x_4015_);
lean_ctor_set(v___x_4027_, 3, v___x_4026_);
v___x_4028_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4029_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4029_, 0, v_a_4006_);
lean_ctor_set(v___x_4029_, 1, v___x_4016_);
lean_ctor_set(v___x_4029_, 2, v___x_4018_);
lean_ctor_set(v___x_4029_, 3, v___x_4028_);
v___x_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v___x_4021_);
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4027_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4025_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4023_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4033_, v___x_4021_);
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4037_ = lean_array_get_size(v_a_4013_);
v___x_4038_ = lean_nat_dec_lt(v___x_4035_, v___x_4037_);
if (v___x_4038_ == 0)
{
lean_dec(v_a_4013_);
v___y_3975_ = v___y_3992_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4021_;
v___y_3978_ = v___y_3990_;
v___y_3979_ = v___y_3991_;
v___y_3980_ = v___x_4034_;
v___y_3981_ = v___x_4036_;
goto v___jp_3974_;
}
else
{
uint8_t v___x_4039_; 
v___x_4039_ = lean_nat_dec_le(v___x_4037_, v___x_4037_);
if (v___x_4039_ == 0)
{
if (v___x_4038_ == 0)
{
lean_dec(v_a_4013_);
v___y_3975_ = v___y_3992_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4021_;
v___y_3978_ = v___y_3990_;
v___y_3979_ = v___y_3991_;
v___y_3980_ = v___x_4034_;
v___y_3981_ = v___x_4036_;
goto v___jp_3974_;
}
else
{
size_t v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_usize_of_nat(v___x_4037_);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4013_, v___x_4011_, v___x_4040_, v___x_4036_);
lean_dec(v_a_4013_);
v___y_3975_ = v___y_3992_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4021_;
v___y_3978_ = v___y_3990_;
v___y_3979_ = v___y_3991_;
v___y_3980_ = v___x_4034_;
v___y_3981_ = v___x_4041_;
goto v___jp_3974_;
}
}
else
{
size_t v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_usize_of_nat(v___x_4037_);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4013_, v___x_4011_, v___x_4042_, v___x_4036_);
lean_dec(v_a_4013_);
v___y_3975_ = v___y_3992_;
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4021_;
v___y_3978_ = v___y_3990_;
v___y_3979_ = v___y_3991_;
v___y_3980_ = v___x_4034_;
v___y_3981_ = v___x_4043_;
goto v___jp_3974_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v___x_4008_);
lean_dec(v_a_4006_);
lean_dec(v___x_4003_);
lean_dec(v_a_4001_);
lean_dec(v_a_3998_);
lean_dec_ref(v___f_3973_);
lean_dec(v_remove_3941_);
lean_dec(v_add_3940_);
v_a_4044_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4012_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4012_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4062_, lean_object* v_star_4063_, lean_object* v_add_4064_, lean_object* v_remove_4065_, lean_object* v_use_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
uint8_t v_noDefaults_boxed_4072_; uint8_t v_star_boxed_4073_; lean_object* v_res_4074_; 
v_noDefaults_boxed_4072_ = lean_unbox(v_noDefaults_4062_);
v_star_boxed_4073_ = lean_unbox(v_star_4063_);
v_res_4074_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4072_, v_star_boxed_4073_, v_add_4064_, v_remove_4065_, v_use_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4075_, size_t v_i_4076_, lean_object* v_bs_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4075_, v_i_4076_, v_bs_4077_, v___y_4080_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4084_, lean_object* v_i_4085_, lean_object* v_bs_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_sz_boxed_4092_; size_t v_i_boxed_4093_; lean_object* v_res_4094_; 
v_sz_boxed_4092_ = lean_unbox_usize(v_sz_4084_);
lean_dec(v_sz_4084_);
v_i_boxed_4093_ = lean_unbox_usize(v_i_4085_);
lean_dec(v_i_4085_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4092_, v_i_boxed_4093_, v_bs_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4094_;
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
res = l_Lean_Meta_SolveByElim_initFn_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_();
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
