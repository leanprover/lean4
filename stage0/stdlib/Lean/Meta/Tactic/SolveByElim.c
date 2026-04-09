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
v___x_757_ = lean_float_of_nat(v___y_754_);
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
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___x_680_, v___x_681_, v___x_682_, v_options_689_, v___x_751_, v___y_753_, v___f_683_, v___x_765_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
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
v___y_768_ = v_a_817_;
v___y_769_ = v___x_820_;
v_a_770_ = v___x_868_;
goto v___jp_767_;
}
else
{
v___y_773_ = v_a_817_;
v___y_774_ = v___x_820_;
v___y_775_ = v___x_866_;
goto v___jp_772_;
}
}
else
{
v___y_773_ = v_a_817_;
v___y_774_ = v___x_820_;
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
size_t v_x_838__boxed_1496_; size_t v_x_839__boxed_1497_; lean_object* v_res_1498_; 
v_x_838__boxed_1496_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_x_839__boxed_1497_ = lean_unbox_usize(v_x_1493_);
lean_dec(v_x_1493_);
v_res_1498_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1491_, v_x_838__boxed_1496_, v_x_839__boxed_1497_, v_x_1494_, v_x_1495_);
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
lean_object* v___x_1510_; lean_object* v_mctx_1511_; lean_object* v_cache_1512_; lean_object* v_zetaDeltaFVarIds_1513_; lean_object* v_postponed_1514_; lean_object* v_diag_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1543_; 
v___x_1510_ = lean_st_ref_take(v___y_1508_);
v_mctx_1511_ = lean_ctor_get(v___x_1510_, 0);
v_cache_1512_ = lean_ctor_get(v___x_1510_, 1);
v_zetaDeltaFVarIds_1513_ = lean_ctor_get(v___x_1510_, 2);
v_postponed_1514_ = lean_ctor_get(v___x_1510_, 3);
v_diag_1515_ = lean_ctor_get(v___x_1510_, 4);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1517_ = v___x_1510_;
v_isShared_1518_ = v_isSharedCheck_1543_;
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
v_isShared_1518_ = v_isSharedCheck_1543_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_depth_1519_; lean_object* v_levelAssignDepth_1520_; lean_object* v_lmvarCounter_1521_; lean_object* v_mvarCounter_1522_; lean_object* v_lDecls_1523_; lean_object* v_decls_1524_; lean_object* v_userNames_1525_; lean_object* v_lAssignment_1526_; lean_object* v_eAssignment_1527_; lean_object* v_dAssignment_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1542_; 
v_depth_1519_ = lean_ctor_get(v_mctx_1511_, 0);
v_levelAssignDepth_1520_ = lean_ctor_get(v_mctx_1511_, 1);
v_lmvarCounter_1521_ = lean_ctor_get(v_mctx_1511_, 2);
v_mvarCounter_1522_ = lean_ctor_get(v_mctx_1511_, 3);
v_lDecls_1523_ = lean_ctor_get(v_mctx_1511_, 4);
v_decls_1524_ = lean_ctor_get(v_mctx_1511_, 5);
v_userNames_1525_ = lean_ctor_get(v_mctx_1511_, 6);
v_lAssignment_1526_ = lean_ctor_get(v_mctx_1511_, 7);
v_eAssignment_1527_ = lean_ctor_get(v_mctx_1511_, 8);
v_dAssignment_1528_ = lean_ctor_get(v_mctx_1511_, 9);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_mctx_1511_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1530_ = v_mctx_1511_;
v_isShared_1531_ = v_isSharedCheck_1542_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_dAssignment_1528_);
lean_inc(v_eAssignment_1527_);
lean_inc(v_lAssignment_1526_);
lean_inc(v_userNames_1525_);
lean_inc(v_decls_1524_);
lean_inc(v_lDecls_1523_);
lean_inc(v_mvarCounter_1522_);
lean_inc(v_lmvarCounter_1521_);
lean_inc(v_levelAssignDepth_1520_);
lean_inc(v_depth_1519_);
lean_dec(v_mctx_1511_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1542_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1527_, v_mvarId_1506_, v_val_1507_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 8, v___x_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_depth_1519_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_levelAssignDepth_1520_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_lmvarCounter_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_mvarCounter_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_lDecls_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 5, v_decls_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 6, v_userNames_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 7, v_lAssignment_1526_);
lean_ctor_set(v_reuseFailAlloc_1541_, 8, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1541_, 9, v_dAssignment_1528_);
v___x_1534_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1534_);
v___x_1536_ = v___x_1517_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_cache_1512_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_zetaDeltaFVarIds_1513_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_postponed_1514_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_diag_1515_);
v___x_1536_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_st_ref_set(v___y_1508_, v___x_1536_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1544_, lean_object* v_val_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1544_, v_val_1545_, v___y_1546_);
lean_dec(v___y_1546_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
lean_inc(v_g_1549_);
v___x_1555_ = l_Lean_MVarId_getType(v_g_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = lean_box(0);
v___x_1558_ = l_Lean_Meta_synthInstance(v_a_1556_, v___x_1557_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1558_);
v___x_1560_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1549_, v_a_1559_, v___y_1551_);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1569_);
v___x_1562_ = v___x_1560_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v___x_1560_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_g_1549_);
v_a_1570_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1558_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1558_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_g_1549_);
v_a_1578_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1555_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1555_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1594_){
_start:
{
lean_object* v___f_1595_; lean_object* v___x_1596_; 
v___f_1595_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1596_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1594_, v___f_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1597_, lean_object* v_val_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1597_, v_val_1598_, v___y_1600_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1605_, lean_object* v_val_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1605_, v_val_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1614_, v_x_1615_, v_x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, size_t v_x_1620_, size_t v_x_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1619_, v_x_1620_, v_x_1621_, v_x_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
size_t v_x_1169__boxed_1631_; size_t v_x_1170__boxed_1632_; lean_object* v_res_1633_; 
v_x_1169__boxed_1631_ = lean_unbox_usize(v_x_1627_);
lean_dec(v_x_1627_);
v_x_1170__boxed_1632_ = lean_unbox_usize(v_x_1628_);
lean_dec(v_x_1628_);
v_res_1633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1625_, v_x_1626_, v_x_1169__boxed_1631_, v_x_1170__boxed_1632_, v_x_1629_, v_x_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1634_, lean_object* v_n_1635_, lean_object* v_k_1636_, lean_object* v_v_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1635_, v_k_1636_, v_v_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1639_, size_t v_depth_1640_, lean_object* v_keys_1641_, lean_object* v_vals_1642_, lean_object* v_heq_1643_, lean_object* v_i_1644_, lean_object* v_entries_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1640_, v_keys_1641_, v_vals_1642_, v_i_1644_, v_entries_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1647_, lean_object* v_depth_1648_, lean_object* v_keys_1649_, lean_object* v_vals_1650_, lean_object* v_heq_1651_, lean_object* v_i_1652_, lean_object* v_entries_1653_){
_start:
{
size_t v_depth_boxed_1654_; lean_object* v_res_1655_; 
v_depth_boxed_1654_ = lean_unbox_usize(v_depth_1648_);
lean_dec(v_depth_1648_);
v_res_1655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1647_, v_depth_boxed_1654_, v_keys_1649_, v_vals_1650_, v_heq_1651_, v_i_1652_, v_entries_1653_);
lean_dec_ref(v_vals_1650_);
lean_dec_ref(v_keys_1649_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1657_, v_x_1658_, v_x_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1662_, lean_object* v_discharge_1663_, lean_object* v_g_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; 
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc(v_g_1664_);
v___x_1670_ = lean_apply_6(v_discharge_1662_, v_g_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, lean_box(0));
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_dec(v_g_1664_);
lean_dec_ref(v_discharge_1663_);
return v___x_1670_;
}
else
{
lean_object* v_a_1671_; uint8_t v___y_1673_; uint8_t v___x_1675_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
v___x_1675_ = l_Lean_Exception_isInterrupt(v_a_1671_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; 
v___x_1676_ = l_Lean_Exception_isRuntime(v_a_1671_);
v___y_1673_ = v___x_1676_;
goto v___jp_1672_;
}
else
{
lean_dec(v_a_1671_);
v___y_1673_ = v___x_1675_;
goto v___jp_1672_;
}
v___jp_1672_:
{
if (v___y_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref(v___x_1670_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
v___x_1674_ = lean_apply_6(v_discharge_1663_, v_g_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, lean_box(0));
return v___x_1674_;
}
else
{
lean_dec(v_g_1664_);
lean_dec_ref(v_discharge_1663_);
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1677_, lean_object* v_discharge_1678_, lean_object* v_g_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1677_, v_discharge_1678_, v_g_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1686_, lean_object* v_discharge_1687_){
_start:
{
lean_object* v_toApplyRulesConfig_1688_; lean_object* v_toBacktrackConfig_1689_; uint8_t v_backtracking_1690_; uint8_t v_intro_1691_; uint8_t v_constructor_1692_; uint8_t v_suggestions_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1725_; 
v_toApplyRulesConfig_1688_ = lean_ctor_get(v_cfg_1686_, 0);
lean_inc_ref(v_toApplyRulesConfig_1688_);
v_toBacktrackConfig_1689_ = lean_ctor_get(v_toApplyRulesConfig_1688_, 0);
lean_inc_ref(v_toBacktrackConfig_1689_);
v_backtracking_1690_ = lean_ctor_get_uint8(v_cfg_1686_, sizeof(void*)*1);
v_intro_1691_ = lean_ctor_get_uint8(v_cfg_1686_, sizeof(void*)*1 + 1);
v_constructor_1692_ = lean_ctor_get_uint8(v_cfg_1686_, sizeof(void*)*1 + 2);
v_suggestions_1693_ = lean_ctor_get_uint8(v_cfg_1686_, sizeof(void*)*1 + 3);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_cfg_1686_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_cfg_1686_, 0);
lean_dec(v_unused_1726_);
v___x_1695_ = v_cfg_1686_;
v_isShared_1696_ = v_isSharedCheck_1725_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v_cfg_1686_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1725_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_toApplyConfig_1697_; uint8_t v_transparency_1698_; uint8_t v_symm_1699_; uint8_t v_exfalso_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1723_; 
v_toApplyConfig_1697_ = lean_ctor_get(v_toApplyRulesConfig_1688_, 1);
v_transparency_1698_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1688_, sizeof(void*)*2);
v_symm_1699_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1688_, sizeof(void*)*2 + 1);
v_exfalso_1700_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1688_, sizeof(void*)*2 + 2);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_toApplyRulesConfig_1688_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v_toApplyRulesConfig_1688_, 0);
lean_dec(v_unused_1724_);
v___x_1702_ = v_toApplyRulesConfig_1688_;
v_isShared_1703_ = v_isSharedCheck_1723_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_toApplyConfig_1697_);
lean_dec(v_toApplyRulesConfig_1688_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1723_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_maxDepth_1704_; lean_object* v_proc_1705_; lean_object* v_suspend_1706_; lean_object* v_discharge_1707_; uint8_t v_commitIndependentGoals_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1722_; 
v_maxDepth_1704_ = lean_ctor_get(v_toBacktrackConfig_1689_, 0);
v_proc_1705_ = lean_ctor_get(v_toBacktrackConfig_1689_, 1);
v_suspend_1706_ = lean_ctor_get(v_toBacktrackConfig_1689_, 2);
v_discharge_1707_ = lean_ctor_get(v_toBacktrackConfig_1689_, 3);
v_commitIndependentGoals_1708_ = lean_ctor_get_uint8(v_toBacktrackConfig_1689_, sizeof(void*)*4);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_toBacktrackConfig_1689_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1710_ = v_toBacktrackConfig_1689_;
v_isShared_1711_ = v_isSharedCheck_1722_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_discharge_1707_);
lean_inc(v_suspend_1706_);
lean_inc(v_proc_1705_);
lean_inc(v_maxDepth_1704_);
lean_dec(v_toBacktrackConfig_1689_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1722_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___f_1712_; lean_object* v___x_1714_; 
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1712_, 0, v_discharge_1687_);
lean_closure_set(v___f_1712_, 1, v_discharge_1707_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 3, v___f_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_maxDepth_1704_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_proc_1705_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_suspend_1706_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v___f_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*4, v_commitIndependentGoals_1708_);
v___x_1714_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1714_);
v___x_1716_ = v___x_1702_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_toApplyConfig_1697_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*2, v_transparency_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*2 + 1, v_symm_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*2 + 2, v_exfalso_1700_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1716_);
v___x_1718_ = v___x_1695_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*1, v_backtracking_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*1 + 1, v_intro_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*1 + 2, v_constructor_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*1 + 3, v_suggestions_1693_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = 1;
v___x_1734_ = l_Lean_Meta_intro1Core(v_g_1727_, v___x_1733_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1753_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1753_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1753_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1751_; 
v_snd_1739_ = lean_ctor_get(v_a_1735_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_a_1735_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v_a_1735_, 0);
lean_dec(v_unused_1752_);
v___x_1741_ = v_a_1735_;
v_isShared_1742_ = v_isSharedCheck_1751_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_dec(v_a_1735_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1751_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = lean_box(0);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 1);
lean_ctor_set(v___x_1741_, 1, v___x_1743_);
lean_ctor_set(v___x_1741_, 0, v_snd_1739_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_snd_1739_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1746_);
v___x_1748_ = v___x_1737_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1734_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1734_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1770_){
_start:
{
lean_object* v___f_1771_; lean_object* v___x_1772_; 
v___f_1771_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1772_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1770_, v___f_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1784_ = l_Lean_MVarId_constructor(v_g_1777_, v___x_1783_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1793_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1784_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1784_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1810_){
_start:
{
lean_object* v___f_1811_; lean_object* v___x_1812_; 
v___f_1811_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1812_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1810_, v___f_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
lean_inc(v_g_1815_);
v___x_1821_ = l_Lean_MVarId_getType(v_g_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_Meta_synthInstance(v_a_1822_, v___x_1823_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1834_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1815_, v_a_1825_, v___y_1817_);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v___x_1826_, 0);
lean_dec(v_unused_1835_);
v___x_1828_ = v___x_1826_;
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
else
{
lean_dec(v___x_1826_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_g_1815_);
v_a_1836_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1824_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1824_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_g_1815_);
v_a_1844_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1821_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1821_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1860_){
_start:
{
lean_object* v___f_1861_; lean_object* v___x_1862_; 
v___f_1861_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1862_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1860_, v___f_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v___x_1866_; 
v___x_1866_ = l_Lean_Expr_hasMVar(v_e_1863_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_e_1863_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v_mctx_1869_; lean_object* v___x_1870_; lean_object* v_fst_1871_; lean_object* v_snd_1872_; lean_object* v___x_1873_; lean_object* v_cache_1874_; lean_object* v_zetaDeltaFVarIds_1875_; lean_object* v_postponed_1876_; lean_object* v_diag_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1886_; 
v___x_1868_ = lean_st_ref_get(v___y_1864_);
v_mctx_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_mctx_1869_);
lean_dec(v___x_1868_);
v___x_1870_ = l_Lean_instantiateMVarsCore(v_mctx_1869_, v_e_1863_);
v_fst_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_fst_1871_);
v_snd_1872_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_snd_1872_);
lean_dec_ref(v___x_1870_);
v___x_1873_ = lean_st_ref_take(v___y_1864_);
v_cache_1874_ = lean_ctor_get(v___x_1873_, 1);
v_zetaDeltaFVarIds_1875_ = lean_ctor_get(v___x_1873_, 2);
v_postponed_1876_ = lean_ctor_get(v___x_1873_, 3);
v_diag_1877_ = lean_ctor_get(v___x_1873_, 4);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1873_, 0);
lean_dec(v_unused_1887_);
v___x_1879_ = v___x_1873_;
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_diag_1877_);
lean_inc(v_postponed_1876_);
lean_inc(v_zetaDeltaFVarIds_1875_);
lean_inc(v_cache_1874_);
lean_dec(v___x_1873_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1886_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_snd_1872_);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_snd_1872_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_zetaDeltaFVarIds_1875_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v_postponed_1876_);
lean_ctor_set(v_reuseFailAlloc_1885_, 4, v_diag_1877_);
v___x_1882_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_st_ref_set(v___y_1864_, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_fst_1871_);
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1888_, v___y_1889_);
lean_dec(v___y_1889_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1892_, v___y_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1906_, v_x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1930_, v_x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1938_, lean_object* v_mvarId_1939_, lean_object* v_x_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1939_, v_x_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_mvarId_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1947_, v_mvarId_1948_, v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_ref_1962_; lean_object* v___x_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_ref_1962_ = lean_ctor_get(v___y_1959_, 5);
v___x_1963_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2_spec__3_spec__6(v_msg_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
lean_inc(v_ref_1962_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_ref_1962_);
lean_ctor_set(v___x_1968_, 1, v_a_1964_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = l_List_reverse___redArg(v_x_1981_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
else
{
lean_object* v_head_1989_; lean_object* v_tail_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2010_; 
v_head_1989_ = lean_ctor_get(v_x_1980_, 0);
v_tail_1990_ = lean_ctor_get(v_x_1980_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_x_1980_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1992_ = v_x_1980_;
v_isShared_1993_ = v_isSharedCheck_2010_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_tail_1990_);
lean_inc(v_head_1989_);
lean_dec(v_x_1980_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2010_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc(v_head_1989_);
v___x_1994_ = l_Lean_Expr_mvar___override(v_head_1989_);
v___x_1995_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_1995_, 0, v___x_1994_);
v___x_1996_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_1989_, v___x_1995_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_x_1981_);
lean_ctor_set(v___x_1992_, 0, v_a_1997_);
v___x_1999_ = v___x_1992_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1997_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_x_1981_);
v___x_1999_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
v_x_1980_ = v_tail_1990_;
v_x_1981_ = v___x_1999_;
goto _start;
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_del_object(v___x_1992_);
lean_dec(v_tail_1990_);
lean_dec(v_x_1981_);
v_a_2002_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1996_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1996_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2011_, v_x_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2018_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2022_, lean_object* v_proc_2023_, lean_object* v_orig_2024_, lean_object* v_goals_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_box(0);
lean_inc(v_orig_2024_);
v___x_2032_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2024_, v___x_2031_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2032_);
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
v___x_2034_ = lean_apply_6(v_test_2022_, v_a_2033_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, lean_box(0));
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; uint8_t v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = lean_unbox(v_a_2035_);
lean_dec(v_a_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_goals_2025_);
lean_dec(v_orig_2024_);
lean_dec_ref(v_proc_2023_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2038_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2037_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v___x_2047_; 
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
v___x_2047_ = lean_apply_7(v_proc_2023_, v_orig_2024_, v_goals_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, lean_box(0));
return v___x_2047_;
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_goals_2025_);
lean_dec(v_orig_2024_);
lean_dec_ref(v_proc_2023_);
v_a_2048_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2034_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2034_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_goals_2025_);
lean_dec(v_orig_2024_);
lean_dec_ref(v_proc_2023_);
lean_dec_ref(v_test_2022_);
v_a_2056_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2032_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2032_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2064_, lean_object* v_proc_2065_, lean_object* v_orig_2066_, lean_object* v_goals_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2064_, v_proc_2065_, v_orig_2066_, v_goals_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2074_, lean_object* v_test_2075_){
_start:
{
lean_object* v_toApplyRulesConfig_2076_; lean_object* v_toBacktrackConfig_2077_; uint8_t v_backtracking_2078_; uint8_t v_intro_2079_; uint8_t v_constructor_2080_; uint8_t v_suggestions_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2113_; 
v_toApplyRulesConfig_2076_ = lean_ctor_get(v_cfg_2074_, 0);
lean_inc_ref(v_toApplyRulesConfig_2076_);
v_toBacktrackConfig_2077_ = lean_ctor_get(v_toApplyRulesConfig_2076_, 0);
lean_inc_ref(v_toBacktrackConfig_2077_);
v_backtracking_2078_ = lean_ctor_get_uint8(v_cfg_2074_, sizeof(void*)*1);
v_intro_2079_ = lean_ctor_get_uint8(v_cfg_2074_, sizeof(void*)*1 + 1);
v_constructor_2080_ = lean_ctor_get_uint8(v_cfg_2074_, sizeof(void*)*1 + 2);
v_suggestions_2081_ = lean_ctor_get_uint8(v_cfg_2074_, sizeof(void*)*1 + 3);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_cfg_2074_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v_cfg_2074_, 0);
lean_dec(v_unused_2114_);
v___x_2083_ = v_cfg_2074_;
v_isShared_2084_ = v_isSharedCheck_2113_;
goto v_resetjp_2082_;
}
else
{
lean_dec(v_cfg_2074_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2113_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_toApplyConfig_2085_; uint8_t v_transparency_2086_; uint8_t v_symm_2087_; uint8_t v_exfalso_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2111_; 
v_toApplyConfig_2085_ = lean_ctor_get(v_toApplyRulesConfig_2076_, 1);
v_transparency_2086_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2076_, sizeof(void*)*2);
v_symm_2087_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2076_, sizeof(void*)*2 + 1);
v_exfalso_2088_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2076_, sizeof(void*)*2 + 2);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_toApplyRulesConfig_2076_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v_toApplyRulesConfig_2076_, 0);
lean_dec(v_unused_2112_);
v___x_2090_ = v_toApplyRulesConfig_2076_;
v_isShared_2091_ = v_isSharedCheck_2111_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_toApplyConfig_2085_);
lean_dec(v_toApplyRulesConfig_2076_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2111_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_maxDepth_2092_; lean_object* v_proc_2093_; lean_object* v_suspend_2094_; lean_object* v_discharge_2095_; uint8_t v_commitIndependentGoals_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2110_; 
v_maxDepth_2092_ = lean_ctor_get(v_toBacktrackConfig_2077_, 0);
v_proc_2093_ = lean_ctor_get(v_toBacktrackConfig_2077_, 1);
v_suspend_2094_ = lean_ctor_get(v_toBacktrackConfig_2077_, 2);
v_discharge_2095_ = lean_ctor_get(v_toBacktrackConfig_2077_, 3);
v_commitIndependentGoals_2096_ = lean_ctor_get_uint8(v_toBacktrackConfig_2077_, sizeof(void*)*4);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_toBacktrackConfig_2077_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2098_ = v_toBacktrackConfig_2077_;
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_discharge_2095_);
lean_inc(v_suspend_2094_);
lean_inc(v_proc_2093_);
lean_inc(v_maxDepth_2092_);
lean_dec(v_toBacktrackConfig_2077_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2110_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___f_2100_; lean_object* v___x_2102_; 
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2100_, 0, v_test_2075_);
lean_closure_set(v___f_2100_, 1, v_proc_2093_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___f_2100_);
v___x_2102_ = v___x_2098_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_maxDepth_2092_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___f_2100_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_suspend_2094_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_discharge_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2109_, sizeof(void*)*4, v_commitIndependentGoals_2096_);
v___x_2102_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2104_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2102_);
v___x_2104_ = v___x_2090_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_toApplyConfig_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*2, v_transparency_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*2 + 1, v_symm_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*2 + 2, v_exfalso_2088_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2104_);
v___x_2106_ = v___x_2083_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1, v_backtracking_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1 + 1, v_intro_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1 + 2, v_constructor_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2107_, sizeof(void*)*1 + 3, v_suggestions_2081_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2115_, lean_object* v_msg_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2123_, v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2132_, lean_object* v_sols_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0));
lean_inc(v_sols_2133_);
v___x_2140_ = l_List_any___redArg(v_sols_2133_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc(v___y_2135_);
lean_inc_ref(v___y_2134_);
v___x_2141_ = lean_apply_6(v_test_2132_, v_sols_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, lean_box(0));
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_sols_2133_);
lean_dec_ref(v_test_2132_);
v___x_2142_ = lean_box(v___x_2140_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2144_, lean_object* v_sols_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2144_, v_sols_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2152_, lean_object* v_test_2153_){
_start:
{
lean_object* v___f_2154_; lean_object* v___x_2155_; 
v___f_2154_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2154_, 0, v_test_2153_);
v___x_2155_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2152_, v___f_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_e_2156_, lean_object* v_s_2157_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_Expr_occurs(v_e_2156_, v_s_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_e_2159_, lean_object* v_s_2160_){
_start:
{
uint8_t v_res_2161_; lean_object* v_r_2162_; 
v_res_2161_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_e_2159_, v_s_2160_);
lean_dec_ref(v_s_2160_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object* v_sols_2163_, lean_object* v_e_2164_){
_start:
{
lean_object* v___f_2165_; uint8_t v___x_2166_; 
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2165_, 0, v_e_2164_);
v___x_2166_ = l_List_any___redArg(v_sols_2163_, v___f_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object* v_sols_2167_, lean_object* v_e_2168_){
_start:
{
uint8_t v_res_2169_; lean_object* v_r_2170_; 
v_res_2169_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(v_sols_2167_, v_e_2168_);
v_r_2170_ = lean_box(v_res_2169_);
return v_r_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object* v_use_2171_, lean_object* v_sols_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___f_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___f_2178_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2178_, 0, v_sols_2172_);
v___x_2179_ = l_List_all___redArg(v_use_2171_, v___f_2178_);
v___x_2180_ = lean_box(v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object* v_use_2182_, lean_object* v_sols_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(v_use_2182_, v_sols_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2190_, lean_object* v_use_2191_){
_start:
{
lean_object* v___f_2192_; lean_object* v___x_2193_; 
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2192_, 0, v_use_2191_);
v___x_2193_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2190_, v___f_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2194_){
_start:
{
lean_object* v___y_2196_; lean_object* v_toApplyRulesConfig_2197_; uint8_t v_backtracking_2198_; uint8_t v_intro_2199_; uint8_t v_constructor_2200_; uint8_t v_suggestions_2201_; uint8_t v_intro_2205_; 
v_intro_2205_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1 + 1);
if (v_intro_2205_ == 0)
{
lean_object* v_toApplyRulesConfig_2206_; uint8_t v_backtracking_2207_; uint8_t v_constructor_2208_; uint8_t v_suggestions_2209_; 
v_toApplyRulesConfig_2206_ = lean_ctor_get(v_cfg_2194_, 0);
lean_inc_ref(v_toApplyRulesConfig_2206_);
v_backtracking_2207_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1);
v_constructor_2208_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1 + 2);
v_suggestions_2209_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1 + 3);
v___y_2196_ = v_cfg_2194_;
v_toApplyRulesConfig_2197_ = v_toApplyRulesConfig_2206_;
v_backtracking_2198_ = v_backtracking_2207_;
v_intro_2199_ = v_intro_2205_;
v_constructor_2200_ = v_constructor_2208_;
v_suggestions_2201_ = v_suggestions_2209_;
goto v___jp_2195_;
}
else
{
lean_object* v_toApplyRulesConfig_2210_; uint8_t v_backtracking_2211_; uint8_t v_constructor_2212_; uint8_t v_suggestions_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2227_; 
v_toApplyRulesConfig_2210_ = lean_ctor_get(v_cfg_2194_, 0);
v_backtracking_2211_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1);
v_constructor_2212_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1 + 2);
v_suggestions_2213_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*1 + 3);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_cfg_2194_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2215_ = v_cfg_2194_;
v_isShared_2216_ = v_isSharedCheck_2227_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_toApplyRulesConfig_2210_);
lean_dec(v_cfg_2194_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2227_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
uint8_t v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = 0;
if (v_isShared_2216_ == 0)
{
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_toApplyRulesConfig_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*1, v_backtracking_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*1 + 2, v_constructor_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, sizeof(void*)*1 + 3, v_suggestions_2213_);
v___x_2219_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v_toApplyRulesConfig_2221_; uint8_t v_backtracking_2222_; uint8_t v_intro_2223_; uint8_t v_constructor_2224_; uint8_t v_suggestions_2225_; 
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*1 + 1, v___x_2217_);
v___x_2220_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2219_);
v_toApplyRulesConfig_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc_ref(v_toApplyRulesConfig_2221_);
v_backtracking_2222_ = lean_ctor_get_uint8(v___x_2220_, sizeof(void*)*1);
v_intro_2223_ = lean_ctor_get_uint8(v___x_2220_, sizeof(void*)*1 + 1);
v_constructor_2224_ = lean_ctor_get_uint8(v___x_2220_, sizeof(void*)*1 + 2);
v_suggestions_2225_ = lean_ctor_get_uint8(v___x_2220_, sizeof(void*)*1 + 3);
v___y_2196_ = v___x_2220_;
v_toApplyRulesConfig_2197_ = v_toApplyRulesConfig_2221_;
v_backtracking_2198_ = v_backtracking_2222_;
v_intro_2199_ = v_intro_2223_;
v_constructor_2200_ = v_constructor_2224_;
v_suggestions_2201_ = v_suggestions_2225_;
goto v___jp_2195_;
}
}
}
v___jp_2195_:
{
if (v_constructor_2200_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2197_);
return v___y_2196_;
}
else
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec_ref(v___y_2196_);
v___x_2202_ = 0;
v___x_2203_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2203_, 0, v_toApplyRulesConfig_2197_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*1, v_backtracking_2198_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*1 + 1, v_intro_2199_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*1 + 2, v___x_2202_);
lean_ctor_set_uint8(v___x_2203_, sizeof(void*)*1 + 3, v_suggestions_2201_);
v___x_2204_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2203_);
return v___x_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2228_, lean_object* v_x_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
if (lean_obj_tag(v_x_2228_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = l_List_reverse___redArg(v_x_2229_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
else
{
lean_object* v_head_2239_; lean_object* v_tail_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2258_; 
v_head_2239_ = lean_ctor_get(v_x_2228_, 0);
v_tail_2240_ = lean_ctor_get(v_x_2228_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_x_2228_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2242_ = v_x_2228_;
v_isShared_2243_ = v_isSharedCheck_2258_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_tail_2240_);
lean_inc(v_head_2239_);
lean_dec(v_x_2228_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2258_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; 
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
v___x_2244_ = lean_apply_7(v_head_2239_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, lean_box(0));
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2244_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 1, v_x_2229_);
lean_ctor_set(v___x_2242_, 0, v_a_2245_);
v___x_2247_ = v___x_2242_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2245_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_x_2229_);
v___x_2247_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
v_x_2228_ = v_tail_2240_;
v_x_2229_ = v___x_2247_;
goto _start;
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_del_object(v___x_2242_);
lean_dec(v_tail_2240_);
lean_dec(v_x_2229_);
v_a_2250_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2244_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2244_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2259_, lean_object* v_x_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2259_, v_x_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2269_, lean_object* v_cfg_2270_, lean_object* v_lemmas_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
v___x_2279_ = lean_apply_8(v_ctx_2269_, v_cfg_2270_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, lean_box(0));
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = lean_box(0);
v___x_2282_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2271_, v___x_2281_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2291_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = l_List_appendTR___redArg(v_a_2280_, v_a_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2287_);
v___x_2289_ = v___x_2285_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
lean_dec(v_a_2280_);
return v___x_2282_;
}
}
else
{
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v_lemmas_2271_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2292_, lean_object* v_cfg_2293_, lean_object* v_lemmas_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2292_, v_cfg_2293_, v_lemmas_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2303_){
_start:
{
uint8_t v___x_2304_; 
v___x_2304_ = 0;
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2305_){
_start:
{
uint8_t v_res_2306_; lean_object* v_r_2307_; 
v_res_2306_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2305_);
lean_dec(v_x_2305_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2308_, lean_object* v___x_2309_, lean_object* v___x_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2308_, v___x_2309_, v___x_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2325_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2325_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_fst_2321_; lean_object* v___x_2323_; 
v_fst_2321_ = lean_ctor_get(v_a_2317_, 0);
lean_inc(v_fst_2321_);
lean_dec(v_a_2317_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_fst_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_fst_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2316_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2316_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2334_, v___x_2335_, v___x_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2357_, lean_object* v_g_2358_, lean_object* v_lemmas_2359_, lean_object* v_ctx_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___f_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; 
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2366_, 0, v_ctx_2360_);
lean_closure_set(v___f_2366_, 1, v_cfg_2357_);
lean_closure_set(v___f_2366_, 2, v_lemmas_2359_);
v___x_2367_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2368_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2369_, 0, v___f_2366_);
lean_closure_set(v___f_2369_, 1, v___x_2367_);
lean_closure_set(v___f_2369_, 2, v___x_2368_);
v___x_2370_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2358_, v___f_2369_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2371_, lean_object* v_g_2372_, lean_object* v_lemmas_2373_, lean_object* v_ctx_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2371_, v_g_2372_, v_lemmas_2373_, v_ctx_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2381_, lean_object* v_lemmas_2382_, lean_object* v_ctx_2383_, lean_object* v_g_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2390_; 
lean_inc(v_g_2384_);
lean_inc_ref(v_cfg_2381_);
v___x_2390_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2381_, v_g_2384_, v_lemmas_2382_, v_ctx_2383_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_toApplyRulesConfig_2391_; lean_object* v_a_2392_; lean_object* v_toApplyConfig_2393_; uint8_t v_transparency_2394_; lean_object* v___x_2395_; 
v_toApplyRulesConfig_2391_ = lean_ctor_get(v_cfg_2381_, 0);
lean_inc_ref(v_toApplyRulesConfig_2391_);
lean_dec_ref(v_cfg_2381_);
v_a_2392_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2390_);
v_toApplyConfig_2393_ = lean_ctor_get(v_toApplyRulesConfig_2391_, 1);
lean_inc_ref(v_toApplyConfig_2393_);
v_transparency_2394_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2391_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2391_);
v___x_2395_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2393_, v_transparency_2394_, v_a_2392_, v_g_2384_, v_a_2386_, v_a_2388_);
return v___x_2395_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_g_2384_);
lean_dec_ref(v_cfg_2381_);
v_a_2396_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2390_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2390_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2404_, lean_object* v_lemmas_2405_, lean_object* v_ctx_2406_, lean_object* v_g_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2404_, v_lemmas_2405_, v_ctx_2406_, v_g_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2414_, lean_object* v_lemmas_2415_, lean_object* v_ctx_2416_, lean_object* v_g_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; 
lean_inc(v_g_2417_);
lean_inc_ref(v_cfg_2414_);
v___x_2423_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2414_, v_g_2417_, v_lemmas_2415_, v_ctx_2416_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_toApplyRulesConfig_2424_; lean_object* v_a_2425_; lean_object* v_toApplyConfig_2426_; uint8_t v_transparency_2427_; lean_object* v___x_2428_; 
v_toApplyRulesConfig_2424_ = lean_ctor_get(v_cfg_2414_, 0);
lean_inc_ref(v_toApplyRulesConfig_2424_);
lean_dec_ref(v_cfg_2414_);
v_a_2425_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2425_);
lean_dec_ref(v___x_2423_);
v_toApplyConfig_2426_ = lean_ctor_get(v_toApplyRulesConfig_2424_, 1);
lean_inc_ref(v_toApplyConfig_2426_);
v_transparency_2427_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2424_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2424_);
v___x_2428_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2426_, v_transparency_2427_, v_a_2425_, v_g_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
return v___x_2428_;
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_g_2417_);
lean_dec_ref(v_cfg_2414_);
v_a_2429_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2423_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2423_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2437_, lean_object* v_lemmas_2438_, lean_object* v_ctx_2439_, lean_object* v_g_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2437_, v_lemmas_2438_, v_ctx_2439_, v_g_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2447_, lean_object* v_i_2448_, lean_object* v_k_2449_){
_start:
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = lean_array_get_size(v_keys_2447_);
v___x_2451_ = lean_nat_dec_lt(v_i_2448_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_dec(v_i_2448_);
return v___x_2451_;
}
else
{
lean_object* v_k_x27_2452_; uint8_t v___x_2453_; 
v_k_x27_2452_ = lean_array_fget_borrowed(v_keys_2447_, v_i_2448_);
v___x_2453_ = l_Lean_instBEqMVarId_beq(v_k_2449_, v_k_x27_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_unsigned_to_nat(1u);
v___x_2455_ = lean_nat_add(v_i_2448_, v___x_2454_);
lean_dec(v_i_2448_);
v_i_2448_ = v___x_2455_;
goto _start;
}
else
{
lean_dec(v_i_2448_);
return v___x_2453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2457_, lean_object* v_i_2458_, lean_object* v_k_2459_){
_start:
{
uint8_t v_res_2460_; lean_object* v_r_2461_; 
v_res_2460_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2457_, v_i_2458_, v_k_2459_);
lean_dec(v_k_2459_);
lean_dec_ref(v_keys_2457_);
v_r_2461_ = lean_box(v_res_2460_);
return v_r_2461_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2462_, size_t v_x_2463_, lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2462_) == 0)
{
lean_object* v_es_2465_; lean_object* v___x_2466_; size_t v___x_2467_; size_t v___x_2468_; size_t v___x_2469_; lean_object* v_j_2470_; lean_object* v___x_2471_; 
v_es_2465_ = lean_ctor_get(v_x_2462_, 0);
v___x_2466_ = lean_box(2);
v___x_2467_ = ((size_t)5ULL);
v___x_2468_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2469_ = lean_usize_land(v_x_2463_, v___x_2468_);
v_j_2470_ = lean_usize_to_nat(v___x_2469_);
v___x_2471_ = lean_array_get_borrowed(v___x_2466_, v_es_2465_, v_j_2470_);
lean_dec(v_j_2470_);
switch(lean_obj_tag(v___x_2471_))
{
case 0:
{
lean_object* v_key_2472_; uint8_t v___x_2473_; 
v_key_2472_ = lean_ctor_get(v___x_2471_, 0);
v___x_2473_ = l_Lean_instBEqMVarId_beq(v_x_2464_, v_key_2472_);
return v___x_2473_;
}
case 1:
{
lean_object* v_node_2474_; size_t v___x_2475_; 
v_node_2474_ = lean_ctor_get(v___x_2471_, 0);
v___x_2475_ = lean_usize_shift_right(v_x_2463_, v___x_2467_);
v_x_2462_ = v_node_2474_;
v_x_2463_ = v___x_2475_;
goto _start;
}
default: 
{
uint8_t v___x_2477_; 
v___x_2477_ = 0;
return v___x_2477_;
}
}
}
else
{
lean_object* v_ks_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
v_ks_2478_ = lean_ctor_get(v_x_2462_, 0);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2478_, v___x_2479_, v_x_2464_);
return v___x_2480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2481_, lean_object* v_x_2482_, lean_object* v_x_2483_){
_start:
{
size_t v_x_2218__boxed_2484_; uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_x_2218__boxed_2484_ = lean_unbox_usize(v_x_2482_);
lean_dec(v_x_2482_);
v_res_2485_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2481_, v_x_2218__boxed_2484_, v_x_2483_);
lean_dec(v_x_2483_);
lean_dec_ref(v_x_2481_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2487_, lean_object* v_x_2488_){
_start:
{
uint64_t v___x_2489_; size_t v___x_2490_; uint8_t v___x_2491_; 
v___x_2489_ = l_Lean_instHashableMVarId_hash(v_x_2488_);
v___x_2490_ = lean_uint64_to_usize(v___x_2489_);
v___x_2491_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2487_, v___x_2490_, v_x_2488_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
uint8_t v_res_2494_; lean_object* v_r_2495_; 
v_res_2494_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2492_, v_x_2493_);
lean_dec(v_x_2493_);
lean_dec_ref(v_x_2492_);
v_r_2495_ = lean_box(v_res_2494_);
return v_r_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v_mctx_2500_; lean_object* v_eAssignment_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2499_ = lean_st_ref_get(v___y_2497_);
v_mctx_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_ref(v_mctx_2500_);
lean_dec(v___x_2499_);
v_eAssignment_2501_ = lean_ctor_get(v_mctx_2500_, 8);
lean_inc_ref(v_eAssignment_2501_);
lean_dec_ref(v_mctx_2500_);
v___x_2502_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2501_, v_mvarId_2496_);
lean_dec_ref(v_eAssignment_2501_);
v___x_2503_ = lean_box(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec(v_mvarId_2505_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
return v_x_2509_;
}
else
{
lean_object* v_head_2511_; lean_object* v_tail_2512_; lean_object* v___x_2513_; 
v_head_2511_ = lean_ctor_get(v_x_2510_, 0);
lean_inc(v_head_2511_);
v_tail_2512_ = lean_ctor_get(v_x_2510_, 1);
lean_inc(v_tail_2512_);
lean_dec_ref(v_x_2510_);
v___x_2513_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2509_, v_head_2511_);
v_x_2509_ = v___x_2513_;
v_x_2510_ = v_tail_2512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2515_, lean_object* v_a_2516_, uint8_t v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
if (lean_obj_tag(v_a_2518_) == 0)
{
if (lean_obj_tag(v_a_2519_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec(v_a_2516_);
lean_dec_ref(v_f_2515_);
v___x_2526_ = lean_box(v_a_2517_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v_a_2520_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
else
{
lean_object* v_head_2529_; lean_object* v_tail_2530_; 
v_head_2529_ = lean_ctor_get(v_a_2519_, 0);
lean_inc(v_head_2529_);
v_tail_2530_ = lean_ctor_get(v_a_2519_, 1);
lean_inc(v_tail_2530_);
lean_dec_ref(v_a_2519_);
v_a_2518_ = v_head_2529_;
v_a_2519_ = v_tail_2530_;
goto _start;
}
}
else
{
lean_object* v_head_2532_; lean_object* v_tail_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2576_; 
v_head_2532_ = lean_ctor_get(v_a_2518_, 0);
v_tail_2533_ = lean_ctor_get(v_a_2518_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2535_ = v_a_2518_;
v_isShared_2536_ = v_isSharedCheck_2576_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_tail_2533_);
lean_inc(v_head_2532_);
lean_dec(v_a_2518_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2576_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2575_; 
v___x_2537_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2532_, v___y_2522_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2575_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2575_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_unbox(v_a_2538_);
lean_dec(v_a_2538_);
if (v___x_2542_ == 0)
{
lean_object* v_zero_2543_; uint8_t v_isZero_2544_; 
v_zero_2543_ = lean_unsigned_to_nat(0u);
v_isZero_2544_ = lean_nat_dec_eq(v_a_2516_, v_zero_2543_);
if (v_isZero_2544_ == 1)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_del_object(v___x_2535_);
lean_dec(v_a_2516_);
lean_dec_ref(v_f_2515_);
v___x_2545_ = lean_array_push(v_a_2520_, v_head_2532_);
v___x_2546_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2545_, v_tail_2533_);
v___x_2547_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2546_, v_a_2519_);
v___x_2548_ = lean_box(v_a_2517_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
lean_ctor_set(v___x_2549_, 1, v___x_2547_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2549_);
v___x_2551_ = v___x_2540_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_del_object(v___x_2540_);
lean_inc_ref(v_f_2515_);
lean_inc(v_head_2532_);
v___x_2553_ = lean_apply_1(v_f_2515_, v_head_2532_);
v___x_2554_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___redArg(v___x_2553_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v_one_2556_; lean_object* v_n_2557_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2554_);
v_one_2556_ = lean_unsigned_to_nat(1u);
v_n_2557_ = lean_nat_sub(v_a_2516_, v_one_2556_);
lean_dec(v_a_2516_);
if (lean_obj_tag(v_a_2555_) == 0)
{
lean_object* v___x_2558_; 
lean_del_object(v___x_2535_);
v___x_2558_ = lean_array_push(v_a_2520_, v_head_2532_);
v_a_2516_ = v_n_2557_;
v_a_2518_ = v_tail_2533_;
v_a_2520_ = v___x_2558_;
goto _start;
}
else
{
lean_object* v_val_2560_; uint8_t v___x_2561_; lean_object* v___x_2563_; 
lean_dec(v_head_2532_);
v_val_2560_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_val_2560_);
lean_dec_ref(v_a_2555_);
v___x_2561_ = 1;
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v_a_2519_);
lean_ctor_set(v___x_2535_, 0, v_tail_2533_);
v___x_2563_ = v___x_2535_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_tail_2533_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_a_2519_);
v___x_2563_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
v_a_2516_ = v_n_2557_;
v_a_2517_ = v___x_2561_;
v_a_2518_ = v_val_2560_;
v_a_2519_ = v___x_2563_;
goto _start;
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_del_object(v___x_2535_);
lean_dec(v_tail_2533_);
lean_dec(v_head_2532_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2516_);
lean_dec_ref(v_f_2515_);
v_a_2566_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2554_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2554_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
else
{
lean_del_object(v___x_2540_);
lean_del_object(v___x_2535_);
lean_dec(v_head_2532_);
v_a_2518_ = v_tail_2533_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
uint8_t v_a_2299__boxed_2588_; lean_object* v_res_2589_; 
v_a_2299__boxed_2588_ = lean_unbox(v_a_2579_);
v_res_2589_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2577_, v_a_2578_, v_a_2299__boxed_2588_, v_a_2580_, v_a_2581_, v_a_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2590_, size_t v_i_2591_, size_t v_stop_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_a_2600_; uint8_t v___x_2604_; 
v___x_2604_ = lean_usize_dec_eq(v_i_2591_, v_stop_2592_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2608_; 
v___x_2605_ = lean_array_uget_borrowed(v_as_2590_, v_i_2591_);
v___x_2608_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2605_, v___y_2595_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; uint8_t v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = lean_unbox(v_a_2609_);
lean_dec(v_a_2609_);
if (v___x_2610_ == 0)
{
goto v___jp_2606_;
}
else
{
v_a_2600_ = v_b_2593_;
goto v___jp_2599_;
}
}
else
{
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2611_; uint8_t v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2608_);
v___x_2612_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
if (v___x_2612_ == 0)
{
v_a_2600_ = v_b_2593_;
goto v___jp_2599_;
}
else
{
goto v___jp_2606_;
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_b_2593_);
v_a_2613_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2608_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2608_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
v___jp_2606_:
{
lean_object* v___x_2607_; 
lean_inc(v___x_2605_);
v___x_2607_ = lean_array_push(v_b_2593_, v___x_2605_);
v_a_2600_ = v___x_2607_;
goto v___jp_2599_;
}
}
else
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_b_2593_);
return v___x_2621_;
}
v___jp_2599_:
{
size_t v___x_2601_; size_t v___x_2602_; 
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2591_, v___x_2601_);
v_i_2591_ = v___x_2602_;
v_b_2593_ = v_a_2600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2622_, lean_object* v_i_2623_, lean_object* v_stop_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
size_t v_i_boxed_2631_; size_t v_stop_boxed_2632_; lean_object* v_res_2633_; 
v_i_boxed_2631_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_stop_boxed_2632_ = lean_unbox_usize(v_stop_2624_);
lean_dec(v_stop_2624_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2622_, v_i_boxed_2631_, v_stop_boxed_2632_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_as_2622_);
return v_res_2633_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2637_ = lean_array_to_list(v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2638_, lean_object* v_goals_2639_, lean_object* v_maxIters_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
uint8_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2646_ = 0;
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2650_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2638_, v_maxIters_2640_, v___x_2646_, v_goals_2639_, v___x_2647_, v___x_2649_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2700_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2700_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2700_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2699_; 
v_fst_2655_ = lean_ctor_get(v_a_2651_, 0);
v_snd_2656_ = lean_ctor_get(v_a_2651_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2658_ = v_a_2651_;
v_isShared_2659_ = v_isSharedCheck_2699_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_inc(v_fst_2655_);
lean_dec(v_a_2651_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2699_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_____do__lift_2661_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = lean_array_get_size(v_snd_2656_);
v___x_2670_ = lean_nat_dec_lt(v___x_2648_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_del_object(v___x_2658_);
lean_dec(v_snd_2656_);
lean_del_object(v___x_2653_);
v___x_2671_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v_fst_2655_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
else
{
uint8_t v___x_2674_; 
v___x_2674_ = lean_nat_dec_le(v___x_2669_, v___x_2669_);
if (v___x_2674_ == 0)
{
if (v___x_2670_ == 0)
{
lean_dec(v_snd_2656_);
v_____do__lift_2661_ = v___x_2649_;
goto v___jp_2660_;
}
else
{
size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((size_t)0ULL);
v___x_2676_ = lean_usize_of_nat(v___x_2669_);
v___x_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2656_, v___x_2675_, v___x_2676_, v___x_2649_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v_snd_2656_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2677_);
v_____do__lift_2661_ = v_a_2678_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_del_object(v___x_2658_);
lean_dec(v_fst_2655_);
lean_del_object(v___x_2653_);
v_a_2679_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2677_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = lean_usize_of_nat(v___x_2669_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2656_, v___x_2687_, v___x_2688_, v___x_2649_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v_snd_2656_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2689_);
v_____do__lift_2661_ = v_a_2690_;
goto v___jp_2660_;
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_del_object(v___x_2658_);
lean_dec(v_fst_2655_);
lean_del_object(v___x_2653_);
v_a_2691_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2689_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2689_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
v___jp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_array_to_list(v_____do__lift_2661_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 1, v___x_2662_);
v___x_2664_ = v___x_2658_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_fst_2655_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2666_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2664_);
v___x_2666_ = v___x_2653_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_a_2701_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2650_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2650_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2709_, lean_object* v_goals_2710_, lean_object* v_maxIters_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2709_, v_goals_2710_, v_maxIters_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2717_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2721_, lean_object* v_goals_2722_, lean_object* v_maxIters_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2721_, v_goals_2722_, v_maxIters_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2742_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2742_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2742_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_fst_2734_; uint8_t v___x_2735_; 
v_fst_2734_ = lean_ctor_get(v_a_2730_, 0);
v___x_2735_ = lean_unbox(v_fst_2734_);
if (v___x_2735_ == 1)
{
lean_object* v_snd_2736_; lean_object* v___x_2738_; 
v_snd_2736_ = lean_ctor_get(v_a_2730_, 1);
lean_inc(v_snd_2736_);
lean_dec(v_a_2730_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v_snd_2736_);
v___x_2738_ = v___x_2732_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_snd_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_del_object(v___x_2732_);
lean_dec(v_a_2730_);
v___x_2740_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2741_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2740_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_a_2743_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2729_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2729_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2751_, lean_object* v_goals_2752_, lean_object* v_maxIters_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2751_, v_goals_2752_, v_maxIters_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2760_, lean_object* v_ctx_2761_, lean_object* v_cfg_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
uint8_t v_backtracking_2769_; 
v_backtracking_2769_ = lean_ctor_get_uint8(v_cfg_2762_, sizeof(void*)*1);
if (v_backtracking_2769_ == 0)
{
lean_object* v_toApplyRulesConfig_2770_; lean_object* v_toBacktrackConfig_2771_; lean_object* v_maxDepth_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_toApplyRulesConfig_2770_ = lean_ctor_get(v_cfg_2762_, 0);
v_toBacktrackConfig_2771_ = lean_ctor_get(v_toApplyRulesConfig_2770_, 0);
v_maxDepth_2772_ = lean_ctor_get(v_toBacktrackConfig_2771_, 0);
lean_inc(v_maxDepth_2772_);
v___x_2773_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2773_, 0, v_cfg_2762_);
lean_closure_set(v___x_2773_, 1, v_lemmas_2760_);
lean_closure_set(v___x_2773_, 2, v_ctx_2761_);
v___x_2774_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2773_, v_a_2763_, v_maxDepth_2772_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
return v___x_2774_;
}
else
{
lean_object* v_toApplyRulesConfig_2775_; lean_object* v_toBacktrackConfig_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_toApplyRulesConfig_2775_ = lean_ctor_get(v_cfg_2762_, 0);
v_toBacktrackConfig_2776_ = lean_ctor_get(v_toApplyRulesConfig_2775_, 0);
lean_inc_ref(v_toBacktrackConfig_2776_);
v___x_2777_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2778_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2778_, 0, v_cfg_2762_);
lean_closure_set(v___x_2778_, 1, v_lemmas_2760_);
lean_closure_set(v___x_2778_, 2, v_ctx_2761_);
v___x_2779_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2776_, v___x_2777_, v___x_2778_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2780_, lean_object* v_ctx_2781_, lean_object* v_cfg_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2780_, v_ctx_2781_, v_cfg_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2790_, v___y_2792_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v_mvarId_2797_);
return v_res_2803_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2804_, lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2805_, v_x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
uint8_t v_res_2811_; lean_object* v_r_2812_; 
v_res_2811_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2808_, v_x_2809_, v_x_2810_);
lean_dec(v_x_2810_);
lean_dec_ref(v_x_2809_);
v_r_2812_ = lean_box(v_res_2811_);
return v_r_2812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2813_, lean_object* v_x_2814_, size_t v_x_2815_, lean_object* v_x_2816_){
_start:
{
uint8_t v___x_2817_; 
v___x_2817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2814_, v_x_2815_, v_x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_){
_start:
{
size_t v_x_2759__boxed_2822_; uint8_t v_res_2823_; lean_object* v_r_2824_; 
v_x_2759__boxed_2822_ = lean_unbox_usize(v_x_2820_);
lean_dec(v_x_2820_);
v_res_2823_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2818_, v_x_2819_, v_x_2759__boxed_2822_, v_x_2821_);
lean_dec(v_x_2821_);
lean_dec_ref(v_x_2819_);
v_r_2824_ = lean_box(v_res_2823_);
return v_r_2824_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2825_, lean_object* v_keys_2826_, lean_object* v_vals_2827_, lean_object* v_heq_2828_, lean_object* v_i_2829_, lean_object* v_k_2830_){
_start:
{
uint8_t v___x_2831_; 
v___x_2831_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2826_, v_i_2829_, v_k_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2832_, lean_object* v_keys_2833_, lean_object* v_vals_2834_, lean_object* v_heq_2835_, lean_object* v_i_2836_, lean_object* v_k_2837_){
_start:
{
uint8_t v_res_2838_; lean_object* v_r_2839_; 
v_res_2838_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2832_, v_keys_2833_, v_vals_2834_, v_heq_2835_, v_i_2836_, v_k_2837_);
lean_dec(v_k_2837_);
lean_dec_ref(v_vals_2834_);
lean_dec_ref(v_keys_2833_);
v_r_2839_ = lean_box(v_res_2838_);
return v_r_2839_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec_ref(v_x_2851_);
return v_res_2857_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2860_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__1));
v___x_2861_ = l_Lean_Name_append(v___x_2860_, v___x_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2862_, lean_object* v_lemmas_2863_, lean_object* v_ctx_2864_, lean_object* v_goals_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_cfg_2871_; lean_object* v___x_2872_; 
v_cfg_2871_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2862_);
lean_inc(v_goals_2865_);
lean_inc_ref(v_cfg_2871_);
lean_inc_ref(v_ctx_2864_);
lean_inc(v_lemmas_2863_);
v___x_2872_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2863_, v_ctx_2864_, v_cfg_2871_, v_goals_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_dec_ref(v_cfg_2871_);
lean_dec(v_goals_2865_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
return v___x_2872_;
}
else
{
lean_object* v_a_2873_; lean_object* v___f_2874_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; uint8_t v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v___y_2882_; lean_object* v_a_2883_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; uint8_t v___y_2901_; lean_object* v___y_2902_; lean_object* v_a_2903_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; uint8_t v___y_2909_; lean_object* v___y_2910_; uint8_t v___y_2911_; lean_object* v___y_2912_; lean_object* v_a_2913_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v_a_2930_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; uint8_t v___y_2936_; uint8_t v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; uint8_t v___y_2975_; uint8_t v___x_3028_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
v___f_2874_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3028_ = l_Lean_Exception_isInterrupt(v_a_2873_);
if (v___x_3028_ == 0)
{
uint8_t v___x_3029_; 
v___x_3029_ = l_Lean_Exception_isRuntime(v_a_2873_);
v___y_2975_ = v___x_3029_;
goto v___jp_2974_;
}
else
{
lean_dec(v_a_2873_);
v___y_2975_ = v___x_3028_;
goto v___jp_2974_;
}
v___jp_2875_:
{
lean_object* v___x_2884_; double v___x_2885_; double v___x_2886_; double v___x_2887_; double v___x_2888_; double v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2884_ = lean_io_mono_nanos_now();
v___x_2885_ = lean_float_of_nat(v___y_2877_);
v___x_2886_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__2);
v___x_2887_ = lean_float_div(v___x_2885_, v___x_2886_);
v___x_2888_ = lean_float_of_nat(v___x_2884_);
v___x_2889_ = lean_float_div(v___x_2888_, v___x_2886_);
v___x_2890_ = lean_box_float(v___x_2887_);
v___x_2891_ = lean_box_float(v___x_2889_);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_a_2883_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
lean_inc_ref(v___y_2878_);
lean_inc(v___y_2876_);
v___x_2894_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2876_, v___y_2881_, v___y_2878_, v___y_2880_, v___y_2879_, v___y_2882_, v___f_2874_, v___x_2893_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2894_;
}
v___jp_2895_:
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_a_2903_);
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2898_;
v___y_2879_ = v___y_2901_;
v___y_2880_ = v___y_2900_;
v___y_2881_ = v___y_2899_;
v___y_2882_ = v___y_2902_;
v_a_2883_ = v___x_2904_;
goto v___jp_2875_;
}
v___jp_2905_:
{
lean_object* v___x_2914_; double v___x_2915_; double v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2914_ = lean_io_get_num_heartbeats();
v___x_2915_ = lean_float_of_nat(v___y_2906_);
v___x_2916_ = lean_float_of_nat(v___x_2914_);
v___x_2917_ = lean_box_float(v___x_2915_);
v___x_2918_ = lean_box_float(v___x_2916_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_a_2913_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
lean_inc_ref(v___y_2908_);
lean_inc(v___y_2907_);
v___x_2921_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_2907_, v___y_2911_, v___y_2908_, v___y_2910_, v___y_2909_, v___y_2912_, v___f_2874_, v___x_2920_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2921_;
}
v___jp_2922_:
{
lean_object* v___x_2931_; 
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_a_2930_);
v___y_2906_ = v___y_2923_;
v___y_2907_ = v___y_2924_;
v___y_2908_ = v___y_2925_;
v___y_2909_ = v___y_2928_;
v___y_2910_ = v___y_2927_;
v___y_2911_ = v___y_2926_;
v___y_2912_ = v___y_2929_;
v_a_2913_ = v___x_2931_;
goto v___jp_2905_;
}
v___jp_2932_:
{
lean_object* v___x_2940_; lean_object* v_a_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2940_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___redArg(v_a_2869_);
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2943_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v___y_2938_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_io_mono_nanos_now();
v___x_2945_ = l_Lean_MVarId_exfalso(v___y_2933_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2947_, 0, v_a_2946_);
lean_ctor_set(v___x_2947_, 1, v___y_2939_);
v___x_2948_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2863_, v_ctx_2864_, v_cfg_2871_, v___x_2947_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 1);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v___y_2876_ = v___y_2934_;
v___y_2877_ = v___x_2944_;
v___y_2878_ = v___y_2935_;
v___y_2879_ = v___y_2937_;
v___y_2880_ = v___y_2938_;
v___y_2881_ = v___y_2936_;
v___y_2882_ = v_a_2941_;
v_a_2883_ = v___x_2954_;
goto v___jp_2875_;
}
}
}
else
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2948_);
v___y_2896_ = v___y_2934_;
v___y_2897_ = v___x_2944_;
v___y_2898_ = v___y_2935_;
v___y_2899_ = v___y_2936_;
v___y_2900_ = v___y_2938_;
v___y_2901_ = v___y_2937_;
v___y_2902_ = v_a_2941_;
v_a_2903_ = v_a_2957_;
goto v___jp_2895_;
}
}
else
{
lean_object* v_a_2958_; 
lean_dec(v___y_2939_);
lean_dec_ref(v_cfg_2871_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
v_a_2958_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2945_);
v___y_2896_ = v___y_2934_;
v___y_2897_ = v___x_2944_;
v___y_2898_ = v___y_2935_;
v___y_2899_ = v___y_2936_;
v___y_2900_ = v___y_2938_;
v___y_2901_ = v___y_2937_;
v___y_2902_ = v_a_2941_;
v_a_2903_ = v_a_2958_;
goto v___jp_2895_;
}
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_io_get_num_heartbeats();
v___x_2960_ = l_Lean_MVarId_exfalso(v___y_2933_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_a_2961_);
lean_ctor_set(v___x_2962_, 1, v___y_2939_);
v___x_2963_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2863_, v_ctx_2864_, v_cfg_2871_, v___x_2962_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set_tag(v___x_2966_, 1);
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
v___y_2906_ = v___x_2959_;
v___y_2907_ = v___y_2934_;
v___y_2908_ = v___y_2935_;
v___y_2909_ = v___y_2937_;
v___y_2910_ = v___y_2938_;
v___y_2911_ = v___y_2936_;
v___y_2912_ = v_a_2941_;
v_a_2913_ = v___x_2969_;
goto v___jp_2905_;
}
}
}
else
{
lean_object* v_a_2972_; 
v_a_2972_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2972_);
lean_dec_ref(v___x_2963_);
v___y_2923_ = v___x_2959_;
v___y_2924_ = v___y_2934_;
v___y_2925_ = v___y_2935_;
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2938_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v_a_2941_;
v_a_2930_ = v_a_2972_;
goto v___jp_2922_;
}
}
else
{
lean_object* v_a_2973_; 
lean_dec(v___y_2939_);
lean_dec_ref(v_cfg_2871_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
v_a_2973_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2960_);
v___y_2923_ = v___x_2959_;
v___y_2924_ = v___y_2934_;
v___y_2925_ = v___y_2935_;
v___y_2926_ = v___y_2936_;
v___y_2927_ = v___y_2938_;
v___y_2928_ = v___y_2937_;
v___y_2929_ = v_a_2941_;
v_a_2930_ = v_a_2973_;
goto v___jp_2922_;
}
}
}
v___jp_2974_:
{
if (v___y_2975_ == 0)
{
if (lean_obj_tag(v_goals_2865_) == 1)
{
lean_object* v_tail_2976_; 
v_tail_2976_ = lean_ctor_get(v_goals_2865_, 1);
lean_inc(v_tail_2976_);
if (lean_obj_tag(v_tail_2976_) == 0)
{
lean_object* v_toApplyRulesConfig_2977_; uint8_t v_exfalso_2978_; 
v_toApplyRulesConfig_2977_ = lean_ctor_get(v_cfg_2871_, 0);
lean_inc_ref(v_toApplyRulesConfig_2977_);
v_exfalso_2978_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2977_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_2977_);
if (v_exfalso_2978_ == 1)
{
lean_object* v_options_2979_; uint8_t v_hasTrace_2980_; 
lean_dec_ref(v___x_2872_);
v_options_2979_ = lean_ctor_get(v_a_2868_, 2);
v_hasTrace_2980_ = lean_ctor_get_uint8(v_options_2979_, sizeof(void*)*1);
if (v_hasTrace_2980_ == 0)
{
lean_object* v_head_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2999_; 
v_head_2981_ = lean_ctor_get(v_goals_2865_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_goals_2865_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v_goals_2865_, 1);
lean_dec(v_unused_3000_);
v___x_2983_ = v_goals_2865_;
v_isShared_2984_ = v_isSharedCheck_2999_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_head_2981_);
lean_dec(v_goals_2865_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2999_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_MVarId_exfalso(v_head_2981_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v_a_2986_);
v___x_2988_ = v___x_2983_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2986_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_tail_2976_);
v___x_2988_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; 
v___x_2989_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2863_, v_ctx_2864_, v_cfg_2871_, v___x_2988_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_2989_;
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_del_object(v___x_2983_);
lean_dec_ref(v_cfg_2871_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
v_a_2991_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2985_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2985_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
else
{
lean_object* v_head_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3026_; 
v_head_3001_ = lean_ctor_get(v_goals_2865_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_goals_2865_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v_goals_2865_, 1);
lean_dec(v_unused_3027_);
v___x_3003_ = v_goals_2865_;
v_isShared_3004_ = v_isSharedCheck_3026_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_head_3001_);
lean_dec(v_goals_2865_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3026_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v_inheritedTraceOptions_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_inheritedTraceOptions_3005_ = lean_ctor_get(v_a_2868_, 13);
v___x_3006_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3007_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3008_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1);
v___x_3009_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3005_, v_options_2979_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = l_Lean_trace_profiler;
v___x_3011_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_options_2979_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = l_Lean_MVarId_exfalso(v_head_3001_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v_a_3013_);
v___x_3015_ = v___x_3003_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3013_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_tail_2976_);
v___x_3015_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; 
v___x_3016_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2863_, v_ctx_2864_, v_cfg_2871_, v___x_3015_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_3016_;
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_del_object(v___x_3003_);
lean_dec_ref(v_cfg_2871_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
v_a_3018_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3012_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3012_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_del_object(v___x_3003_);
v___y_2933_ = v_head_3001_;
v___y_2934_ = v___x_3006_;
v___y_2935_ = v___x_3007_;
v___y_2936_ = v_exfalso_2978_;
v___y_2937_ = v___x_3009_;
v___y_2938_ = v_options_2979_;
v___y_2939_ = v_tail_2976_;
goto v___jp_2932_;
}
}
else
{
lean_del_object(v___x_3003_);
v___y_2933_ = v_head_3001_;
v___y_2934_ = v___x_3006_;
v___y_2935_ = v___x_3007_;
v___y_2936_ = v_exfalso_2978_;
v___y_2937_ = v___x_3009_;
v___y_2938_ = v_options_2979_;
v___y_2939_ = v_tail_2976_;
goto v___jp_2932_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2865_);
lean_dec_ref(v_cfg_2871_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
return v___x_2872_;
}
}
else
{
lean_dec_ref(v_goals_2865_);
lean_dec(v_tail_2976_);
lean_dec_ref(v_cfg_2871_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
return v___x_2872_;
}
}
else
{
lean_dec_ref(v_cfg_2871_);
lean_dec(v_goals_2865_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
return v___x_2872_;
}
}
else
{
lean_dec_ref(v_cfg_2871_);
lean_dec(v_goals_2865_);
lean_dec_ref(v_ctx_2864_);
lean_dec(v_lemmas_2863_);
return v___x_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3030_, lean_object* v_lemmas_3031_, lean_object* v_ctx_3032_, lean_object* v_goals_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3030_, v_lemmas_3031_, v_ctx_3032_, v_goals_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
if (lean_obj_tag(v_x_3040_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = l_List_reverse___redArg(v_x_3041_);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
else
{
lean_object* v_head_3049_; lean_object* v_tail_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3073_; 
v_head_3049_ = lean_ctor_get(v_x_3040_, 0);
v_tail_3050_ = lean_ctor_get(v_x_3040_, 1);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_x_3040_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3052_ = v_x_3040_;
v_isShared_3053_ = v_isSharedCheck_3073_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_tail_3050_);
lean_inc(v_head_3049_);
lean_dec(v_x_3040_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3073_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_Expr_applySymm(v_head_3049_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref(v___x_3054_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 1, v_x_3041_);
lean_ctor_set(v___x_3052_, 0, v_a_3055_);
v___x_3057_ = v___x_3052_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3055_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_x_3041_);
v___x_3057_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
v_x_3040_ = v_tail_3050_;
v_x_3041_ = v___x_3057_;
goto _start;
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3072_; 
lean_del_object(v___x_3052_);
v_a_3060_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3062_ = v___x_3054_;
v_isShared_3063_ = v_isSharedCheck_3072_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3054_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3072_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint8_t v___y_3065_; uint8_t v___x_3070_; 
v___x_3070_ = l_Lean_Exception_isInterrupt(v_a_3060_);
if (v___x_3070_ == 0)
{
uint8_t v___x_3071_; 
lean_inc(v_a_3060_);
v___x_3071_ = l_Lean_Exception_isRuntime(v_a_3060_);
v___y_3065_ = v___x_3071_;
goto v___jp_3064_;
}
else
{
v___y_3065_ = v___x_3070_;
goto v___jp_3064_;
}
v___jp_3064_:
{
if (v___y_3065_ == 0)
{
lean_del_object(v___x_3062_);
lean_dec(v_a_3060_);
v_x_3040_ = v_tail_3050_;
goto _start;
}
else
{
lean_object* v___x_3068_; 
lean_dec(v_tail_3050_);
lean_dec(v_x_3041_);
if (v_isShared_3063_ == 0)
{
v___x_3068_ = v___x_3062_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3060_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3074_, lean_object* v_x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3074_, v_x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3082_, lean_object* v_hyps_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
if (v_symm_3082_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_hyps_3083_);
return v___x_3089_;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_box(0);
lean_inc(v_hyps_3083_);
v___x_3091_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3083_, v___x_3090_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3100_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3100_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3100_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3096_ = l_List_appendTR___redArg(v_hyps_3083_, v_a_3092_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3096_);
v___x_3098_ = v___x_3094_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
else
{
lean_dec(v_hyps_3083_);
return v___x_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3101_, lean_object* v_hyps_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
uint8_t v_symm_boxed_3108_; lean_object* v_res_3109_; 
v_symm_boxed_3108_ = lean_unbox(v_symm_3101_);
v_res_3109_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3108_, v_hyps_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3110_, size_t v_sz_3111_, size_t v_i_3112_, lean_object* v_b_3113_){
_start:
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_usize_dec_lt(v_i_3112_, v_sz_3111_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_b_3113_);
return v___x_3116_;
}
else
{
lean_object* v_snd_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3135_; 
v_snd_3117_ = lean_ctor_get(v_b_3113_, 1);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_b_3113_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v_b_3113_, 0);
lean_dec(v_unused_3136_);
v___x_3119_ = v_b_3113_;
v_isShared_3120_ = v_isSharedCheck_3135_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_snd_3117_);
lean_dec(v_b_3113_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3135_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v_a_3123_; lean_object* v_a_3130_; 
v___x_3121_ = lean_box(0);
v_a_3130_ = lean_array_uget_borrowed(v_as_3110_, v_i_3112_);
if (lean_obj_tag(v_a_3130_) == 0)
{
v_a_3123_ = v_snd_3117_;
goto v___jp_3122_;
}
else
{
lean_object* v_val_3131_; uint8_t v___x_3132_; 
v_val_3131_ = lean_ctor_get(v_a_3130_, 0);
v___x_3132_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_inc(v_val_3131_);
v___x_3133_ = l_Lean_LocalDecl_toExpr(v_val_3131_);
v___x_3134_ = lean_array_push(v_snd_3117_, v___x_3133_);
v_a_3123_ = v___x_3134_;
goto v___jp_3122_;
}
else
{
v_a_3123_ = v_snd_3117_;
goto v___jp_3122_;
}
}
v___jp_3122_:
{
lean_object* v___x_3125_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 1, v_a_3123_);
lean_ctor_set(v___x_3119_, 0, v___x_3121_);
v___x_3125_ = v___x_3119_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_a_3123_);
v___x_3125_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
size_t v___x_3126_; size_t v___x_3127_; 
v___x_3126_ = ((size_t)1ULL);
v___x_3127_ = lean_usize_add(v_i_3112_, v___x_3126_);
v_i_3112_ = v___x_3127_;
v_b_3113_ = v___x_3125_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3137_, lean_object* v_sz_3138_, lean_object* v_i_3139_, lean_object* v_b_3140_, lean_object* v___y_3141_){
_start:
{
size_t v_sz_boxed_3142_; size_t v_i_boxed_3143_; lean_object* v_res_3144_; 
v_sz_boxed_3142_ = lean_unbox_usize(v_sz_3138_);
lean_dec(v_sz_3138_);
v_i_boxed_3143_ = lean_unbox_usize(v_i_3139_);
lean_dec(v_i_3139_);
v_res_3144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3137_, v_sz_boxed_3142_, v_i_boxed_3143_, v_b_3140_);
lean_dec_ref(v_as_3137_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3145_, size_t v_sz_3146_, size_t v_i_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
uint8_t v___x_3156_; 
v___x_3156_ = lean_usize_dec_lt(v_i_3147_, v_sz_3146_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_b_3148_);
return v___x_3157_;
}
else
{
lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3176_; 
v_snd_3158_ = lean_ctor_get(v_b_3148_, 1);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_b_3148_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v_b_3148_, 0);
lean_dec(v_unused_3177_);
v___x_3160_ = v_b_3148_;
v_isShared_3161_ = v_isSharedCheck_3176_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_dec(v_b_3148_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3176_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v_a_3164_; lean_object* v_a_3171_; 
v___x_3162_ = lean_box(0);
v_a_3171_ = lean_array_uget_borrowed(v_as_3145_, v_i_3147_);
if (lean_obj_tag(v_a_3171_) == 0)
{
v_a_3164_ = v_snd_3158_;
goto v___jp_3163_;
}
else
{
lean_object* v_val_3172_; uint8_t v___x_3173_; 
v_val_3172_ = lean_ctor_get(v_a_3171_, 0);
v___x_3173_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_inc(v_val_3172_);
v___x_3174_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3175_ = lean_array_push(v_snd_3158_, v___x_3174_);
v_a_3164_ = v___x_3175_;
goto v___jp_3163_;
}
else
{
v_a_3164_ = v_snd_3158_;
goto v___jp_3163_;
}
}
v___jp_3163_:
{
lean_object* v___x_3166_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v_a_3164_);
lean_ctor_set(v___x_3160_, 0, v___x_3162_);
v___x_3166_ = v___x_3160_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_a_3164_);
v___x_3166_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = ((size_t)1ULL);
v___x_3168_ = lean_usize_add(v_i_3147_, v___x_3167_);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3145_, v_sz_3146_, v___x_3168_, v___x_3166_);
return v___x_3169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3178_, lean_object* v_sz_3179_, lean_object* v_i_3180_, lean_object* v_b_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; lean_object* v_res_3191_; 
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3179_);
lean_dec(v_sz_3179_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3180_);
lean_dec(v_i_3180_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3178_, v_sz_boxed_3189_, v_i_boxed_3190_, v_b_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec_ref(v_as_3178_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3192_, size_t v_sz_3193_, size_t v_i_3194_, lean_object* v_b_3195_){
_start:
{
uint8_t v___x_3197_; 
v___x_3197_ = lean_usize_dec_lt(v_i_3194_, v_sz_3193_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v_b_3195_);
return v___x_3198_;
}
else
{
lean_object* v_snd_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3217_; 
v_snd_3199_ = lean_ctor_get(v_b_3195_, 1);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_b_3195_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v_b_3195_, 0);
lean_dec(v_unused_3218_);
v___x_3201_ = v_b_3195_;
v_isShared_3202_ = v_isSharedCheck_3217_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_snd_3199_);
lean_dec(v_b_3195_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3217_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v_a_3205_; lean_object* v_a_3212_; 
v___x_3203_ = lean_box(0);
v_a_3212_ = lean_array_uget_borrowed(v_as_3192_, v_i_3194_);
if (lean_obj_tag(v_a_3212_) == 0)
{
v_a_3205_ = v_snd_3199_;
goto v___jp_3204_;
}
else
{
lean_object* v_val_3213_; uint8_t v___x_3214_; 
v_val_3213_ = lean_ctor_get(v_a_3212_, 0);
v___x_3214_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_inc(v_val_3213_);
v___x_3215_ = l_Lean_LocalDecl_toExpr(v_val_3213_);
v___x_3216_ = lean_array_push(v_snd_3199_, v___x_3215_);
v_a_3205_ = v___x_3216_;
goto v___jp_3204_;
}
else
{
v_a_3205_ = v_snd_3199_;
goto v___jp_3204_;
}
}
v___jp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v_a_3205_);
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3207_ = v___x_3201_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_a_3205_);
v___x_3207_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
size_t v___x_3208_; size_t v___x_3209_; 
v___x_3208_ = ((size_t)1ULL);
v___x_3209_ = lean_usize_add(v_i_3194_, v___x_3208_);
v_i_3194_ = v___x_3209_;
v_b_3195_ = v___x_3207_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3219_, lean_object* v_sz_3220_, lean_object* v_i_3221_, lean_object* v_b_3222_, lean_object* v___y_3223_){
_start:
{
size_t v_sz_boxed_3224_; size_t v_i_boxed_3225_; lean_object* v_res_3226_; 
v_sz_boxed_3224_ = lean_unbox_usize(v_sz_3220_);
lean_dec(v_sz_3220_);
v_i_boxed_3225_ = lean_unbox_usize(v_i_3221_);
lean_dec(v_i_3221_);
v_res_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3219_, v_sz_boxed_3224_, v_i_boxed_3225_, v_b_3222_);
lean_dec_ref(v_as_3219_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3227_, size_t v_sz_3228_, size_t v_i_3229_, lean_object* v_b_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_usize_dec_lt(v_i_3229_, v_sz_3228_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v_b_3230_);
return v___x_3239_;
}
else
{
lean_object* v_snd_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3258_; 
v_snd_3240_ = lean_ctor_get(v_b_3230_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_b_3230_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v_b_3230_, 0);
lean_dec(v_unused_3259_);
v___x_3242_ = v_b_3230_;
v_isShared_3243_ = v_isSharedCheck_3258_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_snd_3240_);
lean_dec(v_b_3230_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3258_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v_a_3246_; lean_object* v_a_3253_; 
v___x_3244_ = lean_box(0);
v_a_3253_ = lean_array_uget_borrowed(v_as_3227_, v_i_3229_);
if (lean_obj_tag(v_a_3253_) == 0)
{
v_a_3246_ = v_snd_3240_;
goto v___jp_3245_;
}
else
{
lean_object* v_val_3254_; uint8_t v___x_3255_; 
v_val_3254_ = lean_ctor_get(v_a_3253_, 0);
v___x_3255_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_inc(v_val_3254_);
v___x_3256_ = l_Lean_LocalDecl_toExpr(v_val_3254_);
v___x_3257_ = lean_array_push(v_snd_3240_, v___x_3256_);
v_a_3246_ = v___x_3257_;
goto v___jp_3245_;
}
else
{
v_a_3246_ = v_snd_3240_;
goto v___jp_3245_;
}
}
v___jp_3245_:
{
lean_object* v___x_3248_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 1, v_a_3246_);
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3248_ = v___x_3242_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_a_3246_);
v___x_3248_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
size_t v___x_3249_; size_t v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_add(v_i_3229_, v___x_3249_);
v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3227_, v_sz_3228_, v___x_3250_, v___x_3248_);
return v___x_3251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3260_, lean_object* v_sz_3261_, lean_object* v_i_3262_, lean_object* v_b_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
size_t v_sz_boxed_3271_; size_t v_i_boxed_3272_; lean_object* v_res_3273_; 
v_sz_boxed_3271_ = lean_unbox_usize(v_sz_3261_);
lean_dec(v_sz_3261_);
v_i_boxed_3272_ = lean_unbox_usize(v_i_3262_);
lean_dec(v_i_3262_);
v_res_3273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3260_, v_sz_boxed_3271_, v_i_boxed_3272_, v_b_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v_as_3260_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_init_3274_, lean_object* v_n_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
if (lean_obj_tag(v_n_3275_) == 0)
{
lean_object* v_cs_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3318_; 
v_cs_3284_ = lean_ctor_get(v_n_3275_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_n_3275_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3286_ = v_n_3275_;
v_isShared_3287_ = v_isSharedCheck_3318_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_cs_3284_);
lean_dec(v_n_3275_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3318_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; size_t v_sz_3290_; size_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3288_ = lean_box(0);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v_b_3276_);
v_sz_3290_ = lean_array_size(v_cs_3284_);
v___x_3291_ = ((size_t)0ULL);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3274_, v_cs_3284_, v_sz_3290_, v___x_3291_, v___x_3289_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec_ref(v_cs_3284_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3309_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3309_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3309_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v_fst_3297_; 
v_fst_3297_ = lean_ctor_get(v_a_3293_, 0);
if (lean_obj_tag(v_fst_3297_) == 0)
{
lean_object* v_snd_3298_; lean_object* v___x_3300_; 
v_snd_3298_ = lean_ctor_get(v_a_3293_, 1);
lean_inc(v_snd_3298_);
lean_dec(v_a_3293_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 1);
lean_ctor_set(v___x_3286_, 0, v_snd_3298_);
v___x_3300_ = v___x_3286_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_snd_3298_);
v___x_3300_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; 
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3300_);
v___x_3302_ = v___x_3295_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_val_3305_; lean_object* v___x_3307_; 
lean_inc_ref(v_fst_3297_);
lean_dec(v_a_3293_);
lean_del_object(v___x_3286_);
v_val_3305_ = lean_ctor_get(v_fst_3297_, 0);
lean_inc(v_val_3305_);
lean_dec_ref(v_fst_3297_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v_val_3305_);
v___x_3307_ = v___x_3295_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_val_3305_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_del_object(v___x_3286_);
v_a_3310_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3292_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3292_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
else
{
lean_object* v_vs_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3353_; 
v_vs_3319_ = lean_ctor_get(v_n_3275_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_n_3275_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3321_ = v_n_3275_;
v_isShared_3322_ = v_isSharedCheck_3353_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_vs_3319_);
lean_dec(v_n_3275_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3353_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; size_t v_sz_3325_; size_t v___x_3326_; lean_object* v___x_3327_; 
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v_b_3276_);
v_sz_3325_ = lean_array_size(v_vs_3319_);
v___x_3326_ = ((size_t)0ULL);
v___x_3327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3319_, v_sz_3325_, v___x_3326_, v___x_3324_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec_ref(v_vs_3319_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3344_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3344_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3344_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_fst_3332_; 
v_fst_3332_ = lean_ctor_get(v_a_3328_, 0);
if (lean_obj_tag(v_fst_3332_) == 0)
{
lean_object* v_snd_3333_; lean_object* v___x_3335_; 
v_snd_3333_ = lean_ctor_get(v_a_3328_, 1);
lean_inc(v_snd_3333_);
lean_dec(v_a_3328_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v_snd_3333_);
v___x_3335_ = v___x_3321_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_snd_3333_);
v___x_3335_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3337_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3335_);
v___x_3337_ = v___x_3330_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3342_; 
lean_inc_ref(v_fst_3332_);
lean_dec(v_a_3328_);
lean_del_object(v___x_3321_);
v_val_3340_ = lean_ctor_get(v_fst_3332_, 0);
lean_inc(v_val_3340_);
lean_dec_ref(v_fst_3332_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v_val_3340_);
v___x_3342_ = v___x_3330_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_val_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_del_object(v___x_3321_);
v_a_3345_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3327_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3327_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_init_3354_, lean_object* v_as_3355_, size_t v_sz_3356_, size_t v_i_3357_, lean_object* v_b_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_usize_dec_lt(v_i_3357_, v_sz_3356_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v_b_3358_);
return v___x_3367_;
}
else
{
lean_object* v_snd_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3402_; 
v_snd_3368_ = lean_ctor_get(v_b_3358_, 1);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_b_3358_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_b_3358_, 0);
lean_dec(v_unused_3403_);
v___x_3370_ = v_b_3358_;
v_isShared_3371_ = v_isSharedCheck_3402_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_snd_3368_);
lean_dec(v_b_3358_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3402_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_a_3372_; lean_object* v___x_3373_; 
v_a_3372_ = lean_array_uget_borrowed(v_as_3355_, v_i_3357_);
lean_inc(v_snd_3368_);
lean_inc(v_a_3372_);
v___x_3373_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3354_, v_a_3372_, v_snd_3368_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3393_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3393_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3393_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
if (lean_obj_tag(v_a_3374_) == 0)
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3378_, 0, v_a_3374_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3378_);
v___x_3380_ = v___x_3370_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_snd_3368_);
v___x_3380_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3382_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3380_);
v___x_3382_ = v___x_3376_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
lean_del_object(v___x_3376_);
lean_dec(v_snd_3368_);
v_a_3385_ = lean_ctor_get(v_a_3374_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v_a_3374_);
v___x_3386_ = lean_box(0);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v_a_3385_);
lean_ctor_set(v___x_3370_, 0, v___x_3386_);
v___x_3388_ = v___x_3370_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_a_3385_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
size_t v___x_3389_; size_t v___x_3390_; 
v___x_3389_ = ((size_t)1ULL);
v___x_3390_ = lean_usize_add(v_i_3357_, v___x_3389_);
v_i_3357_ = v___x_3390_;
v_b_3358_ = v___x_3388_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_del_object(v___x_3370_);
lean_dec(v_snd_3368_);
v_a_3394_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3373_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3373_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_init_3404_, lean_object* v_as_3405_, lean_object* v_sz_3406_, lean_object* v_i_3407_, lean_object* v_b_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
size_t v_sz_boxed_3416_; size_t v_i_boxed_3417_; lean_object* v_res_3418_; 
v_sz_boxed_3416_ = lean_unbox_usize(v_sz_3406_);
lean_dec(v_sz_3406_);
v_i_boxed_3417_ = lean_unbox_usize(v_i_3407_);
lean_dec(v_i_3407_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_init_3404_, v_as_3405_, v_sz_boxed_3416_, v_i_boxed_3417_, v_b_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v_as_3405_);
lean_dec_ref(v_init_3404_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3419_, lean_object* v_n_3420_, lean_object* v_b_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3419_, v_n_3420_, v_b_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v_init_3419_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3430_, lean_object* v_init_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_root_3439_; lean_object* v_tail_3440_; lean_object* v___x_3441_; 
v_root_3439_ = lean_ctor_get(v_t_3430_, 0);
lean_inc_ref(v_root_3439_);
v_tail_3440_ = lean_ctor_get(v_t_3430_, 1);
lean_inc_ref(v_tail_3440_);
lean_dec_ref(v_t_3430_);
lean_inc_ref(v_init_3431_);
v___x_3441_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3431_, v_root_3439_, v_init_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec_ref(v_init_3431_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3478_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3478_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3478_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
if (lean_obj_tag(v_a_3442_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; 
lean_dec_ref(v_tail_3440_);
v_a_3446_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v_a_3442_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v_a_3446_);
v___x_3448_ = v___x_3444_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; size_t v_sz_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
lean_del_object(v___x_3444_);
v_a_3450_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v_a_3442_);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v_a_3450_);
v_sz_3453_ = lean_array_size(v_tail_3440_);
v___x_3454_ = ((size_t)0ULL);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3440_, v_sz_3453_, v___x_3454_, v___x_3452_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec_ref(v_tail_3440_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3469_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3469_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3469_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_fst_3460_; 
v_fst_3460_ = lean_ctor_get(v_a_3456_, 0);
if (lean_obj_tag(v_fst_3460_) == 0)
{
lean_object* v_snd_3461_; lean_object* v___x_3463_; 
v_snd_3461_ = lean_ctor_get(v_a_3456_, 1);
lean_inc(v_snd_3461_);
lean_dec(v_a_3456_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v_snd_3461_);
v___x_3463_ = v___x_3458_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_snd_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
else
{
lean_object* v_val_3465_; lean_object* v___x_3467_; 
lean_inc_ref(v_fst_3460_);
lean_dec(v_a_3456_);
v_val_3465_ = lean_ctor_get(v_fst_3460_, 0);
lean_inc(v_val_3465_);
lean_dec_ref(v_fst_3460_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v_val_3465_);
v___x_3467_ = v___x_3458_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_val_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
v_a_3470_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3455_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3455_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v_tail_3440_);
v_a_3479_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3441_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3441_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3487_, lean_object* v_init_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3487_, v_init_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_lctx_3506_; lean_object* v_decls_3507_; lean_object* v_hs_3508_; lean_object* v___x_3509_; 
v_lctx_3506_ = lean_ctor_get(v___y_3501_, 2);
v_decls_3507_ = lean_ctor_get(v_lctx_3506_, 1);
v_hs_3508_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
lean_inc_ref(v_decls_3507_);
v___x_3509_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3507_, v_hs_3508_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3518_, lean_object* v_cfg_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
if (v_only_3518_ == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_toApplyRulesConfig_3528_; lean_object* v_a_3529_; uint8_t v_symm_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v_toApplyRulesConfig_3528_ = lean_ctor_get(v_cfg_3519_, 0);
v_a_3529_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3527_);
v_symm_3530_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3528_, sizeof(void*)*2 + 1);
v___x_3531_ = lean_array_to_list(v_a_3529_);
v___x_3532_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3530_, v___x_3531_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
return v___x_3532_;
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
v_a_3533_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3527_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3527_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3543_, lean_object* v_cfg_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
uint8_t v_only_boxed_3552_; lean_object* v_res_3553_; 
v_only_boxed_3552_ = lean_unbox(v_only_3543_);
v_res_3553_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3552_, v_cfg_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec_ref(v_cfg_3544_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3554_, lean_object* v_lemmas_3555_, uint8_t v_only_3556_, lean_object* v_g_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_toApplyRulesConfig_3563_; uint8_t v_intro_3564_; uint8_t v_constructor_3565_; uint8_t v_suggestions_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3579_; 
v_toApplyRulesConfig_3563_ = lean_ctor_get(v_cfg_3554_, 0);
v_intro_3564_ = lean_ctor_get_uint8(v_cfg_3554_, sizeof(void*)*1 + 1);
v_constructor_3565_ = lean_ctor_get_uint8(v_cfg_3554_, sizeof(void*)*1 + 2);
v_suggestions_3566_ = lean_ctor_get_uint8(v_cfg_3554_, sizeof(void*)*1 + 3);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_cfg_3554_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3568_ = v_cfg_3554_;
v_isShared_3569_ = v_isSharedCheck_3579_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_toApplyRulesConfig_3563_);
lean_dec(v_cfg_3554_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3579_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3570_; lean_object* v_ctx_3571_; uint8_t v___x_3572_; lean_object* v___x_3574_; 
v___x_3570_ = lean_box(v_only_3556_);
v_ctx_3571_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3571_, 0, v___x_3570_);
v___x_3572_ = 0;
if (v_isShared_3569_ == 0)
{
v___x_3574_ = v___x_3568_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_toApplyRulesConfig_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3578_, sizeof(void*)*1 + 1, v_intro_3564_);
lean_ctor_set_uint8(v_reuseFailAlloc_3578_, sizeof(void*)*1 + 2, v_constructor_3565_);
lean_ctor_set_uint8(v_reuseFailAlloc_3578_, sizeof(void*)*1 + 3, v_suggestions_3566_);
v___x_3574_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_ctor_set_uint8(v___x_3574_, sizeof(void*)*1, v___x_3572_);
v___x_3575_ = lean_box(0);
v___x_3576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3576_, 0, v_g_3557_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3574_, v_lemmas_3555_, v_ctx_3571_, v___x_3576_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
return v___x_3577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3580_, lean_object* v_lemmas_3581_, lean_object* v_only_3582_, lean_object* v_g_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
uint8_t v_only_boxed_3589_; lean_object* v_res_3590_; 
v_only_boxed_3589_ = lean_unbox(v_only_3582_);
v_res_3590_ = l_Lean_MVarId_applyRules(v_cfg_3580_, v_lemmas_3581_, v_only_boxed_3589_, v_g_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3591_, size_t v_sz_3592_, size_t v_i_3593_, lean_object* v_b_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3591_, v_sz_3592_, v_i_3593_, v_b_3594_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3603_, lean_object* v_sz_3604_, lean_object* v_i_3605_, lean_object* v_b_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
size_t v_sz_boxed_3614_; size_t v_i_boxed_3615_; lean_object* v_res_3616_; 
v_sz_boxed_3614_ = lean_unbox_usize(v_sz_3604_);
lean_dec(v_sz_3604_);
v_i_boxed_3615_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_res_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3603_, v_sz_boxed_3614_, v_i_boxed_3615_, v_b_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_as_3603_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3617_, size_t v_sz_3618_, size_t v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3617_, v_sz_3618_, v_i_3619_, v_b_3620_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3629_, lean_object* v_sz_3630_, lean_object* v_i_3631_, lean_object* v_b_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
size_t v_sz_boxed_3640_; size_t v_i_boxed_3641_; lean_object* v_res_3642_; 
v_sz_boxed_3640_ = lean_unbox_usize(v_sz_3630_);
lean_dec(v_sz_3630_);
v_i_boxed_3641_ = lean_unbox_usize(v_i_3631_);
lean_dec(v_i_3631_);
v_res_3642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3629_, v_sz_boxed_3640_, v_i_boxed_3641_, v_b_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v_as_3629_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_box(0);
v___x_3652_ = 1;
v___x_3653_ = l_Lean_Elab_Term_elabTerm(v_t_3643_, v___x_3651_, v___x_3652_, v___x_3652_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_ref_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v_ref_3668_ = lean_ctor_get(v___y_3665_, 5);
v___x_3669_ = 0;
v___x_3670_ = l_Lean_SourceInfo_fromRef(v_ref_3668_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
return v_res_3677_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3679_) == 0)
{
uint8_t v___x_3680_; 
v___x_3680_ = 0;
return v___x_3680_;
}
else
{
lean_object* v_head_3681_; lean_object* v_tail_3682_; uint8_t v___x_3683_; 
v_head_3681_ = lean_ctor_get(v_x_3679_, 0);
v_tail_3682_ = lean_ctor_get(v_x_3679_, 1);
v___x_3683_ = lean_expr_eqv(v_a_3678_, v_head_3681_);
if (v___x_3683_ == 0)
{
v_x_3679_ = v_tail_3682_;
goto _start;
}
else
{
return v___x_3683_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3685_, lean_object* v_x_3686_){
_start:
{
uint8_t v_res_3687_; lean_object* v_r_3688_; 
v_res_3687_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3685_, v_x_3686_);
lean_dec(v_x_3686_);
lean_dec_ref(v_a_3685_);
v_r_3688_ = lean_box(v_res_3687_);
return v_r_3688_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3689_, lean_object* v_x_3690_){
_start:
{
uint8_t v___x_3691_; 
v___x_3691_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3690_, v_ys_3689_);
if (v___x_3691_ == 0)
{
uint8_t v___x_3692_; 
v___x_3692_ = 1;
return v___x_3692_;
}
else
{
uint8_t v___x_3693_; 
v___x_3693_ = 0;
return v___x_3693_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3694_, lean_object* v_x_3695_){
_start:
{
uint8_t v_res_3696_; lean_object* v_r_3697_; 
v_res_3696_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3694_, v_x_3695_);
lean_dec_ref(v_x_3695_);
lean_dec(v_ys_3694_);
v_r_3697_ = lean_box(v_res_3696_);
return v_r_3697_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3698_, lean_object* v_ys_3699_){
_start:
{
lean_object* v___f_3700_; lean_object* v___x_3701_; 
v___f_3700_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3700_, 0, v_ys_3699_);
v___x_3701_ = l_List_filter___redArg(v___f_3700_, v_xs_3698_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = l_List_reverse___redArg(v_x_3703_);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
else
{
lean_object* v_head_3713_; lean_object* v_tail_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3732_; 
v_head_3713_ = lean_ctor_get(v_x_3702_, 0);
v_tail_3714_ = lean_ctor_get(v_x_3702_, 1);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_x_3702_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3716_ = v_x_3702_;
v_isShared_3717_ = v_isSharedCheck_3732_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_tail_3714_);
lean_inc(v_head_3713_);
lean_dec(v_x_3702_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3732_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3713_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref(v___x_3718_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 1, v_x_3703_);
lean_ctor_set(v___x_3716_, 0, v_a_3719_);
v___x_3721_ = v___x_3716_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3719_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_x_3703_);
v___x_3721_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
v_x_3702_ = v_tail_3714_;
v_x_3703_ = v___x_3721_;
goto _start;
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_del_object(v___x_3716_);
lean_dec(v_tail_3714_);
lean_dec(v_x_3703_);
v_a_3724_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3718_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3718_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3733_, v_x_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3743_, uint8_t v_noDefaults_3744_, uint8_t v_star_3745_, lean_object* v_cfg_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
if (v_noDefaults_3744_ == 0)
{
goto v___jp_3754_;
}
else
{
if (v_star_3745_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec(v_remove_3743_);
v___x_3773_ = lean_box(0);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
return v___x_3774_;
}
else
{
goto v___jp_3754_;
}
}
v___jp_3754_:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___x_3755_);
v___x_3757_ = lean_box(0);
v___x_3758_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3743_, v___x_3757_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_toApplyRulesConfig_3759_; lean_object* v_a_3760_; uint8_t v_symm_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_toApplyRulesConfig_3759_ = lean_ctor_get(v_cfg_3746_, 0);
v_a_3760_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3760_);
lean_dec_ref(v___x_3758_);
v_symm_3761_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3759_, sizeof(void*)*2 + 1);
v___x_3762_ = lean_array_to_list(v_a_3756_);
v___x_3763_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3762_, v_a_3760_);
v___x_3764_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3761_, v___x_3763_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3764_;
}
else
{
lean_dec(v_a_3756_);
return v___x_3758_;
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec(v_remove_3743_);
v_a_3765_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3755_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3755_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3775_, lean_object* v_noDefaults_3776_, lean_object* v_star_3777_, lean_object* v_cfg_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
uint8_t v_noDefaults_boxed_3786_; uint8_t v_star_boxed_3787_; lean_object* v_res_3788_; 
v_noDefaults_boxed_3786_ = lean_unbox(v_noDefaults_3776_);
v_star_boxed_3787_ = lean_unbox(v_star_3777_);
v_res_3788_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3775_, v_noDefaults_boxed_3786_, v_star_boxed_3787_, v_cfg_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_cfg_3778_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3789_, size_t v_i_3790_, size_t v_stop_3791_, lean_object* v_b_3792_){
_start:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_usize_dec_eq(v_i_3790_, v_stop_3791_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; size_t v___x_3796_; size_t v___x_3797_; 
v___x_3794_ = lean_array_uget_borrowed(v_as_3789_, v_i_3790_);
v___x_3795_ = l_Array_append___redArg(v_b_3792_, v___x_3794_);
v___x_3796_ = ((size_t)1ULL);
v___x_3797_ = lean_usize_add(v_i_3790_, v___x_3796_);
v_i_3790_ = v___x_3797_;
v_b_3792_ = v___x_3795_;
goto _start;
}
else
{
return v_b_3792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3799_, lean_object* v_i_3800_, lean_object* v_stop_3801_, lean_object* v_b_3802_){
_start:
{
size_t v_i_boxed_3803_; size_t v_stop_boxed_3804_; lean_object* v_res_3805_; 
v_i_boxed_3803_ = lean_unbox_usize(v_i_3800_);
lean_dec(v_i_3800_);
v_stop_boxed_3804_ = lean_unbox_usize(v_stop_3801_);
lean_dec(v_stop_3801_);
v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3799_, v_i_boxed_3803_, v_stop_boxed_3804_, v_b_3802_);
lean_dec_ref(v_as_3799_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
if (lean_obj_tag(v_a_3806_) == 0)
{
lean_object* v___x_3808_; 
v___x_3808_ = l_List_reverse___redArg(v_a_3807_);
return v___x_3808_;
}
else
{
lean_object* v_head_3809_; lean_object* v_tail_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3819_; 
v_head_3809_ = lean_ctor_get(v_a_3806_, 0);
v_tail_3810_ = lean_ctor_get(v_a_3806_, 1);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_a_3806_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3812_ = v_a_3806_;
v_isShared_3813_ = v_isSharedCheck_3819_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_tail_3810_);
lean_inc(v_head_3809_);
lean_dec(v_a_3806_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3819_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3814_, 0, v_head_3809_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 1, v_a_3807_);
lean_ctor_set(v___x_3812_, 0, v___x_3814_);
v___x_3816_ = v___x_3812_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_a_3807_);
v___x_3816_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
v_a_3806_ = v_tail_3810_;
v_a_3807_ = v___x_3816_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3820_, size_t v_i_3821_, lean_object* v_bs_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
uint8_t v___x_3826_; 
v___x_3826_ = lean_usize_dec_lt(v_i_3821_, v_sz_3820_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_bs_3822_);
return v___x_3827_;
}
else
{
lean_object* v_v_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_v_3828_ = lean_array_uget_borrowed(v_bs_3822_, v_i_3821_);
v___x_3829_ = l_Lean_Syntax_getId(v_v_3828_);
v___x_3830_ = l_Lean_labelled(v___x_3829_, v___y_3823_, v___y_3824_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; lean_object* v_bs_x27_3833_; size_t v___x_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
v___x_3832_ = lean_unsigned_to_nat(0u);
v_bs_x27_3833_ = lean_array_uset(v_bs_3822_, v_i_3821_, v___x_3832_);
v___x_3834_ = ((size_t)1ULL);
v___x_3835_ = lean_usize_add(v_i_3821_, v___x_3834_);
v___x_3836_ = lean_array_uset(v_bs_x27_3833_, v_i_3821_, v_a_3831_);
v_i_3821_ = v___x_3835_;
v_bs_3822_ = v___x_3836_;
goto _start;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v_bs_3822_);
v_a_3838_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3830_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3830_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3846_, lean_object* v_i_3847_, lean_object* v_bs_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
size_t v_sz_boxed_3852_; size_t v_i_boxed_3853_; lean_object* v_res_3854_; 
v_sz_boxed_3852_ = lean_unbox_usize(v_sz_3846_);
lean_dec(v_sz_3846_);
v_i_boxed_3853_ = lean_unbox_usize(v_i_3847_);
lean_dec(v_i_3847_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3852_, v_i_boxed_3853_, v_bs_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3855_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
if (lean_obj_tag(v_a_3873_) == 0)
{
lean_object* v___x_3875_; 
v___x_3875_ = l_List_reverse___redArg(v_a_3874_);
return v___x_3875_;
}
else
{
lean_object* v_head_3876_; lean_object* v_tail_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3886_; 
v_head_3876_ = lean_ctor_get(v_a_3873_, 0);
v_tail_3877_ = lean_ctor_get(v_a_3873_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_a_3873_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3879_ = v_a_3873_;
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_tail_3877_);
lean_inc(v_head_3876_);
lean_dec(v_a_3873_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___f_3881_; lean_object* v___x_3883_; 
v___f_3881_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3881_, 0, v_head_3876_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_a_3874_);
lean_ctor_set(v___x_3879_, 0, v___f_3881_);
v___x_3883_ = v___x_3879_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___f_3881_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_a_3874_);
v___x_3883_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
v_a_3873_ = v_tail_3877_;
v_a_3874_ = v___x_3883_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3889_ = l_Lean_stringToMessageData(v___x_3888_);
return v___x_3889_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3892_ = l_String_toRawSubstring_x27(v___x_3891_);
return v___x_3892_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3897_ = l_String_toRawSubstring_x27(v___x_3896_);
return v___x_3897_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3902_ = l_String_toRawSubstring_x27(v___x_3901_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3907_ = l_String_toRawSubstring_x27(v___x_3906_);
return v___x_3907_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3938_ = l_Lean_stringToMessageData(v___x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3939_, uint8_t v_star_3940_, lean_object* v_add_3941_, lean_object* v_remove_3942_, lean_object* v_use_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___f_3974_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; 
v___x_3972_ = lean_box(v_noDefaults_3939_);
v___x_3973_ = lean_box(v_star_3940_);
lean_inc(v_remove_3942_);
v___f_3974_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3974_, 0, v_remove_3942_);
lean_closure_set(v___f_3974_, 1, v___x_3972_);
lean_closure_set(v___f_3974_, 2, v___x_3973_);
if (v_star_3940_ == 0)
{
v___y_3991_ = v_a_3944_;
v___y_3992_ = v_a_3945_;
v___y_3993_ = v_a_3946_;
v___y_3994_ = v_a_3947_;
goto v___jp_3990_;
}
else
{
if (v_noDefaults_3939_ == 0)
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v___f_3974_);
lean_dec_ref(v_use_3943_);
lean_dec(v_remove_3942_);
lean_dec(v_add_3941_);
v___x_4053_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4054_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4053_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
else
{
v___y_3991_ = v_a_3944_;
v___y_3992_ = v_a_3945_;
v___y_3993_ = v_a_3946_;
v___y_3994_ = v_a_3947_;
goto v___jp_3990_;
}
}
v___jp_3949_:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___y_3951_);
lean_ctor_set(v___x_3952_, 1, v___y_3950_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
return v___x_3953_;
}
v___jp_3954_:
{
uint8_t v___x_3961_; 
v___x_3961_ = l_List_isEmpty___redArg(v_remove_3942_);
lean_dec(v_remove_3942_);
if (v___x_3961_ == 0)
{
if (v_noDefaults_3939_ == 0)
{
v___y_3950_ = v___y_3956_;
v___y_3951_ = v___y_3960_;
goto v___jp_3949_;
}
else
{
if (v_star_3940_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3956_);
v___x_3962_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3963_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3962_, v___y_3959_, v___y_3957_, v___y_3955_, v___y_3958_);
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
v___y_3950_ = v___y_3956_;
v___y_3951_ = v___y_3960_;
goto v___jp_3949_;
}
}
}
else
{
v___y_3950_ = v___y_3956_;
v___y_3951_ = v___y_3960_;
goto v___jp_3949_;
}
}
v___jp_3975_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_array_to_list(v___y_3982_);
lean_inc(v___y_3977_);
v___x_3984_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_3983_, v___y_3977_);
if (v_noDefaults_3939_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3941_, v___y_3977_);
v___x_3986_ = l_List_appendTR___redArg(v___x_3985_, v___x_3984_);
v___x_3987_ = l_List_appendTR___redArg(v___x_3986_, v___y_3980_);
v___y_3955_ = v___y_3976_;
v___y_3956_ = v___f_3974_;
v___y_3957_ = v___y_3978_;
v___y_3958_ = v___y_3979_;
v___y_3959_ = v___y_3981_;
v___y_3960_ = v___x_3987_;
goto v___jp_3954_;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
lean_dec(v___y_3980_);
v___x_3988_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3941_, v___y_3977_);
v___x_3989_ = l_List_appendTR___redArg(v___x_3988_, v___x_3984_);
v___y_3955_ = v___y_3976_;
v___y_3956_ = v___f_3974_;
v___y_3957_ = v___y_3978_;
v___y_3958_ = v___y_3979_;
v___y_3959_ = v___y_3981_;
v___y_3960_ = v___x_3989_;
goto v___jp_3954_;
}
}
v___jp_3990_:
{
lean_object* v_ref_3995_; lean_object* v_quotContext_3996_; lean_object* v_currMacroScope_3997_; lean_object* v___x_3998_; lean_object* v_a_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v_a_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v_a_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; size_t v_sz_4011_; size_t v___x_4012_; lean_object* v___x_4013_; 
v_ref_3995_ = lean_ctor_get(v___y_3993_, 5);
v_quotContext_3996_ = lean_ctor_get(v___y_3993_, 10);
v_currMacroScope_3997_ = lean_ctor_get(v___y_3993_, 11);
v___x_3998_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4001_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_4001_);
v___x_4003_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc_n(v_currMacroScope_3997_, 2);
lean_inc_n(v_quotContext_3996_, 2);
v___x_4004_ = l_Lean_addMacroScope(v_quotContext_3996_, v___x_4003_, v_currMacroScope_3997_);
v___x_4005_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4006_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref(v___x_4006_);
v___x_4008_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
v___x_4009_ = l_Lean_addMacroScope(v_quotContext_3996_, v___x_4008_, v_currMacroScope_3997_);
v___x_4010_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4011_ = lean_array_size(v_use_3943_);
v___x_4012_ = ((size_t)0ULL);
v___x_4013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4011_, v___x_4012_, v_use_3943_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4013_);
v___x_4015_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc_n(v_currMacroScope_3997_, 2);
lean_inc_n(v_quotContext_3996_, 2);
v___x_4016_ = l_Lean_addMacroScope(v_quotContext_3996_, v___x_4015_, v_currMacroScope_3997_);
v___x_4017_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4018_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
v___x_4019_ = l_Lean_addMacroScope(v_quotContext_3996_, v___x_4018_, v_currMacroScope_3997_);
v___x_4020_ = 0;
v___x_4021_ = l_Lean_SourceInfo_fromRef(v_ref_3995_, v___x_4020_);
v___x_4022_ = lean_box(0);
v___x_4023_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4021_);
lean_ctor_set(v___x_4024_, 1, v___x_4000_);
lean_ctor_set(v___x_4024_, 2, v___x_4004_);
lean_ctor_set(v___x_4024_, 3, v___x_4023_);
v___x_4025_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4026_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4026_, 0, v_a_3999_);
lean_ctor_set(v___x_4026_, 1, v___x_4005_);
lean_ctor_set(v___x_4026_, 2, v___x_4009_);
lean_ctor_set(v___x_4026_, 3, v___x_4025_);
v___x_4027_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4028_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4028_, 0, v_a_4002_);
lean_ctor_set(v___x_4028_, 1, v___x_4010_);
lean_ctor_set(v___x_4028_, 2, v___x_4016_);
lean_ctor_set(v___x_4028_, 3, v___x_4027_);
v___x_4029_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4030_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4030_, 0, v_a_4007_);
lean_ctor_set(v___x_4030_, 1, v___x_4017_);
lean_ctor_set(v___x_4030_, 2, v___x_4019_);
lean_ctor_set(v___x_4030_, 3, v___x_4029_);
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
lean_ctor_set(v___x_4031_, 1, v___x_4022_);
v___x_4032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4028_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4026_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4024_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4034_, v___x_4022_);
v___x_4036_ = lean_unsigned_to_nat(0u);
v___x_4037_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4038_ = lean_array_get_size(v_a_4014_);
v___x_4039_ = lean_nat_dec_lt(v___x_4036_, v___x_4038_);
if (v___x_4039_ == 0)
{
lean_dec(v_a_4014_);
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4022_;
v___y_3978_ = v___y_3992_;
v___y_3979_ = v___y_3994_;
v___y_3980_ = v___x_4035_;
v___y_3981_ = v___y_3991_;
v___y_3982_ = v___x_4037_;
goto v___jp_3975_;
}
else
{
uint8_t v___x_4040_; 
v___x_4040_ = lean_nat_dec_le(v___x_4038_, v___x_4038_);
if (v___x_4040_ == 0)
{
if (v___x_4039_ == 0)
{
lean_dec(v_a_4014_);
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4022_;
v___y_3978_ = v___y_3992_;
v___y_3979_ = v___y_3994_;
v___y_3980_ = v___x_4035_;
v___y_3981_ = v___y_3991_;
v___y_3982_ = v___x_4037_;
goto v___jp_3975_;
}
else
{
size_t v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_usize_of_nat(v___x_4038_);
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4014_, v___x_4012_, v___x_4041_, v___x_4037_);
lean_dec(v_a_4014_);
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4022_;
v___y_3978_ = v___y_3992_;
v___y_3979_ = v___y_3994_;
v___y_3980_ = v___x_4035_;
v___y_3981_ = v___y_3991_;
v___y_3982_ = v___x_4042_;
goto v___jp_3975_;
}
}
else
{
size_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = lean_usize_of_nat(v___x_4038_);
v___x_4044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4014_, v___x_4012_, v___x_4043_, v___x_4037_);
lean_dec(v_a_4014_);
v___y_3976_ = v___y_3993_;
v___y_3977_ = v___x_4022_;
v___y_3978_ = v___y_3992_;
v___y_3979_ = v___y_3994_;
v___y_3980_ = v___x_4035_;
v___y_3981_ = v___y_3991_;
v___y_3982_ = v___x_4044_;
goto v___jp_3975_;
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v___x_4009_);
lean_dec(v_a_4007_);
lean_dec(v___x_4004_);
lean_dec(v_a_4002_);
lean_dec(v_a_3999_);
lean_dec_ref(v___f_3974_);
lean_dec(v_remove_3942_);
lean_dec(v_add_3941_);
v_a_4045_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4013_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4013_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4063_, lean_object* v_star_4064_, lean_object* v_add_4065_, lean_object* v_remove_4066_, lean_object* v_use_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
uint8_t v_noDefaults_boxed_4073_; uint8_t v_star_boxed_4074_; lean_object* v_res_4075_; 
v_noDefaults_boxed_4073_ = lean_unbox(v_noDefaults_4063_);
v_star_boxed_4074_ = lean_unbox(v_star_4064_);
v_res_4075_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4073_, v_star_boxed_4074_, v_add_4065_, v_remove_4066_, v_use_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4076_, size_t v_i_4077_, lean_object* v_bs_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4076_, v_i_4077_, v_bs_4078_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4085_, lean_object* v_i_4086_, lean_object* v_bs_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
size_t v_sz_boxed_4093_; size_t v_i_boxed_4094_; lean_object* v_res_4095_; 
v_sz_boxed_4093_ = lean_unbox_usize(v_sz_4085_);
lean_dec(v_sz_4085_);
v_i_boxed_4094_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_res_4095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4093_, v_i_boxed_4094_, v_bs_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4095_;
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
