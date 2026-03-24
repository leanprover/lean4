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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "trying to apply: "};
static const lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(lean_object* v_cls_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_options_66_; uint8_t v_hasTrace_67_; 
v_options_66_ = lean_ctor_get(v___y_64_, 2);
v_hasTrace_67_ = lean_ctor_get_uint8(v_options_66_, sizeof(void*)*1);
if (v_hasTrace_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_cls_63_);
v___x_68_ = lean_box(v_hasTrace_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_inheritedTraceOptions_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_inheritedTraceOptions_70_ = lean_ctor_get(v___y_64_, 13);
v___x_71_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___closed__1));
v___x_72_ = l_Lean_Name_append(v___x_71_, v_cls_63_);
v___x_73_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_70_, v_options_66_, v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_box(v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg___boxed(lean_object* v_cls_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(v_cls_76_, v___y_77_);
lean_dec_ref(v___y_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(lean_object* v_cls_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(v_cls_80_, v___y_83_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___boxed(lean_object* v_cls_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1(v_cls_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(32u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_97_ = ((size_t)5ULL);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_unsigned_to_nat(32u);
v___x_100_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_101_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__0);
v___x_102_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_98_);
lean_ctor_set(v___x_102_, 3, v___x_98_);
lean_ctor_set_usize(v___x_102_, 4, v___x_97_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_traceState_106_; lean_object* v_traces_107_; lean_object* v___x_108_; lean_object* v_traceState_109_; lean_object* v_env_110_; lean_object* v_nextMacroScope_111_; lean_object* v_ngen_112_; lean_object* v_auxDeclNGen_113_; lean_object* v_cache_114_; lean_object* v_messages_115_; lean_object* v_infoState_116_; lean_object* v_snapshotTasks_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_136_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_traceState_106_ = lean_ctor_get(v___x_105_, 4);
lean_inc_ref(v_traceState_106_);
lean_dec(v___x_105_);
v_traces_107_ = lean_ctor_get(v_traceState_106_, 0);
lean_inc_ref(v_traces_107_);
lean_dec_ref(v_traceState_106_);
v___x_108_ = lean_st_ref_take(v___y_103_);
v_traceState_109_ = lean_ctor_get(v___x_108_, 4);
v_env_110_ = lean_ctor_get(v___x_108_, 0);
v_nextMacroScope_111_ = lean_ctor_get(v___x_108_, 1);
v_ngen_112_ = lean_ctor_get(v___x_108_, 2);
v_auxDeclNGen_113_ = lean_ctor_get(v___x_108_, 3);
v_cache_114_ = lean_ctor_get(v___x_108_, 5);
v_messages_115_ = lean_ctor_get(v___x_108_, 6);
v_infoState_116_ = lean_ctor_get(v___x_108_, 7);
v_snapshotTasks_117_ = lean_ctor_get(v___x_108_, 8);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_136_ == 0)
{
v___x_119_ = v___x_108_;
v_isShared_120_ = v_isSharedCheck_136_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_snapshotTasks_117_);
lean_inc(v_infoState_116_);
lean_inc(v_messages_115_);
lean_inc(v_cache_114_);
lean_inc(v_traceState_109_);
lean_inc(v_auxDeclNGen_113_);
lean_inc(v_ngen_112_);
lean_inc(v_nextMacroScope_111_);
lean_inc(v_env_110_);
lean_dec(v___x_108_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_136_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint64_t v_tid_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_134_; 
v_tid_121_ = lean_ctor_get_uint64(v_traceState_109_, sizeof(void*)*1);
v_isSharedCheck_134_ = !lean_is_exclusive(v_traceState_109_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_traceState_109_, 0);
lean_dec(v_unused_135_);
v___x_123_ = v_traceState_109_;
v_isShared_124_ = v_isSharedCheck_134_;
goto v_resetjp_122_;
}
else
{
lean_dec(v_traceState_109_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_134_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___closed__1);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_125_);
lean_ctor_set_uint64(v_reuseFailAlloc_133_, sizeof(void*)*1, v_tid_121_);
v___x_127_ = v_reuseFailAlloc_133_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 4, v___x_127_);
v___x_129_ = v___x_119_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_env_110_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_nextMacroScope_111_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_ngen_112_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_auxDeclNGen_113_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_132_, 5, v_cache_114_);
lean_ctor_set(v_reuseFailAlloc_132_, 6, v_messages_115_);
lean_ctor_set(v_reuseFailAlloc_132_, 7, v_infoState_116_);
lean_ctor_set(v_reuseFailAlloc_132_, 8, v_snapshotTasks_117_);
v___x_129_ = v_reuseFailAlloc_132_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_st_ref_set(v___y_103_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v_traces_107_);
return v___x_131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg___boxed(lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(v___y_137_);
lean_dec(v___y_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(v___y_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___boxed(lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2(v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(lean_object* v_opts_152_, lean_object* v_opt_153_){
_start:
{
lean_object* v_name_154_; lean_object* v_defValue_155_; lean_object* v_map_156_; lean_object* v___x_157_; 
v_name_154_ = lean_ctor_get(v_opt_153_, 0);
v_defValue_155_ = lean_ctor_get(v_opt_153_, 1);
v_map_156_ = lean_ctor_get(v_opts_152_, 0);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_156_, v_name_154_);
if (lean_obj_tag(v___x_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = lean_unbox(v_defValue_155_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; 
v_val_159_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_val_159_);
lean_dec_ref(v___x_157_);
if (lean_obj_tag(v_val_159_) == 1)
{
uint8_t v_v_160_; 
v_v_160_ = lean_ctor_get_uint8(v_val_159_, 0);
lean_dec_ref(v_val_159_);
return v_v_160_;
}
else
{
uint8_t v___x_161_; 
lean_dec(v_val_159_);
v___x_161_ = lean_unbox(v_defValue_155_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3___boxed(lean_object* v_opts_162_, lean_object* v_opt_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_opts_162_, v_opt_163_);
lean_dec_ref(v_opt_163_);
lean_dec_ref(v_opts_162_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_saveState___redArg(v___y_168_, v___y_170_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref(v___x_172_);
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_174_ = lean_apply_5(v_x_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, lean_box(0));
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_173_);
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_a_175_);
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
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_213_; 
v_a_184_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_213_ == 0)
{
v___x_186_ = v___x_174_;
v_isShared_187_ = v_isSharedCheck_213_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_174_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_213_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
uint8_t v___y_189_; uint8_t v___x_211_; 
v___x_211_ = l_Lean_Exception_isInterrupt(v_a_184_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
lean_inc(v_a_184_);
v___x_212_ = l_Lean_Exception_isRuntime(v_a_184_);
v___y_189_ = v___x_212_;
goto v___jp_188_;
}
else
{
v___y_189_ = v___x_211_;
goto v___jp_188_;
}
v___jp_188_:
{
if (v___y_189_ == 0)
{
lean_object* v___x_190_; 
lean_del_object(v___x_186_);
lean_dec(v_a_184_);
v___x_190_ = l_Lean_Meta_SavedState_restore___redArg(v_a_173_, v___y_168_, v___y_170_);
lean_dec(v_a_173_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_190_, 0);
lean_dec(v_unused_199_);
v___x_192_ = v___x_190_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_dec(v___x_190_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_200_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_190_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_190_);
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
else
{
lean_object* v___x_209_; 
lean_dec(v_a_173_);
if (v_isShared_187_ == 0)
{
v___x_209_ = v___x_186_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_184_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v_x_166_);
v_a_214_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_172_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_172_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg___boxed(lean_object* v_x_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(v_x_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7(lean_object* v_00_u03b1_229_, lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___boxed(lean_object* v_00_u03b1_237_, lean_object* v_x_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7(v_00_u03b1_237_, v_x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__0));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(lean_object* v_e_248_, lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_255_ = lean_obj_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___closed__1);
v___x_256_ = l_Lean_MessageData_ofExpr(v_e_248_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed(lean_object* v_e_259_, lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0(v_e_259_, v_x_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec_ref(v_x_260_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(lean_object* v_opts_267_, lean_object* v_opt_268_){
_start:
{
lean_object* v_name_269_; lean_object* v_defValue_270_; lean_object* v_map_271_; lean_object* v___x_272_; 
v_name_269_ = lean_ctor_get(v_opt_268_, 0);
v_defValue_270_ = lean_ctor_get(v_opt_268_, 1);
v_map_271_ = lean_ctor_get(v_opts_267_, 0);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_271_, v_name_269_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_inc(v_defValue_270_);
return v_defValue_270_;
}
else
{
lean_object* v_val_273_; 
v_val_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_val_273_);
lean_dec_ref(v___x_272_);
if (lean_obj_tag(v_val_273_) == 3)
{
lean_object* v_v_274_; 
v_v_274_ = lean_ctor_get(v_val_273_, 0);
lean_inc(v_v_274_);
lean_dec_ref(v_val_273_);
return v_v_274_;
}
else
{
lean_dec(v_val_273_);
lean_inc(v_defValue_270_);
return v_defValue_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7___boxed(lean_object* v_opts_275_, lean_object* v_opt_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(v_opts_275_, v_opt_276_);
lean_dec_ref(v_opt_276_);
lean_dec_ref(v_opts_275_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4(lean_object* v_e_278_){
_start:
{
if (lean_obj_tag(v_e_278_) == 0)
{
uint8_t v___x_279_; 
v___x_279_ = 2;
return v___x_279_;
}
else
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4___boxed(lean_object* v_e_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4(v_e_281_);
lean_dec_ref(v_e_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v_x_284_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v_x_284_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v_x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 1);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v_x_284_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v_x_284_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v_x_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 0);
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg___boxed(lean_object* v_x_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_x_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v___x_313_; lean_object* v_mctx_314_; lean_object* v_lctx_315_; lean_object* v_options_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v___x_313_ = lean_st_ref_get(v___y_307_);
v_mctx_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_mctx_314_);
lean_dec(v___x_313_);
v_lctx_315_ = lean_ctor_get(v___y_306_, 2);
v_options_316_ = lean_ctor_get(v___y_308_, 2);
lean_inc_ref(v_options_316_);
lean_inc_ref(v_lctx_315_);
v___x_317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_317_, 0, v_env_312_);
lean_ctor_set(v___x_317_, 1, v_mctx_314_);
lean_ctor_set(v___x_317_, 2, v_lctx_315_);
lean_ctor_set(v___x_317_, 3, v_options_316_);
v___x_318_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_msgData_305_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8___boxed(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(v_msgData_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7(size_t v_sz_327_, size_t v_i_328_, lean_object* v_bs_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_328_, v_sz_327_);
if (v___x_330_ == 0)
{
return v_bs_329_;
}
else
{
lean_object* v_v_331_; lean_object* v_msg_332_; lean_object* v___x_333_; lean_object* v_bs_x27_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_v_331_ = lean_array_uget_borrowed(v_bs_329_, v_i_328_);
v_msg_332_ = lean_ctor_get(v_v_331_, 1);
lean_inc_ref(v_msg_332_);
v___x_333_ = lean_unsigned_to_nat(0u);
v_bs_x27_334_ = lean_array_uset(v_bs_329_, v_i_328_, v___x_333_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_328_, v___x_335_);
v___x_337_ = lean_array_uset(v_bs_x27_334_, v_i_328_, v_msg_332_);
v_i_328_ = v___x_336_;
v_bs_329_ = v___x_337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7___boxed(lean_object* v_sz_339_, lean_object* v_i_340_, lean_object* v_bs_341_){
_start:
{
size_t v_sz_boxed_342_; size_t v_i_boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_339_);
lean_dec(v_sz_339_);
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_res_344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7(v_sz_boxed_342_, v_i_boxed_343_, v_bs_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5(lean_object* v_oldTraces_345_, lean_object* v_data_346_, lean_object* v_ref_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_fileName_354_; lean_object* v_fileMap_355_; lean_object* v_options_356_; lean_object* v_currRecDepth_357_; lean_object* v_maxRecDepth_358_; lean_object* v_ref_359_; lean_object* v_currNamespace_360_; lean_object* v_openDecls_361_; lean_object* v_initHeartbeats_362_; lean_object* v_maxHeartbeats_363_; lean_object* v_quotContext_364_; lean_object* v_currMacroScope_365_; uint8_t v_diag_366_; lean_object* v_cancelTk_x3f_367_; uint8_t v_suppressElabErrors_368_; lean_object* v_inheritedTraceOptions_369_; lean_object* v___x_370_; lean_object* v_traceState_371_; lean_object* v_traces_372_; lean_object* v_ref_373_; lean_object* v___x_374_; lean_object* v___x_375_; size_t v_sz_376_; size_t v___x_377_; lean_object* v___x_378_; lean_object* v_msg_379_; lean_object* v___x_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_418_; 
v_fileName_354_ = lean_ctor_get(v___y_351_, 0);
v_fileMap_355_ = lean_ctor_get(v___y_351_, 1);
v_options_356_ = lean_ctor_get(v___y_351_, 2);
v_currRecDepth_357_ = lean_ctor_get(v___y_351_, 3);
v_maxRecDepth_358_ = lean_ctor_get(v___y_351_, 4);
v_ref_359_ = lean_ctor_get(v___y_351_, 5);
v_currNamespace_360_ = lean_ctor_get(v___y_351_, 6);
v_openDecls_361_ = lean_ctor_get(v___y_351_, 7);
v_initHeartbeats_362_ = lean_ctor_get(v___y_351_, 8);
v_maxHeartbeats_363_ = lean_ctor_get(v___y_351_, 9);
v_quotContext_364_ = lean_ctor_get(v___y_351_, 10);
v_currMacroScope_365_ = lean_ctor_get(v___y_351_, 11);
v_diag_366_ = lean_ctor_get_uint8(v___y_351_, sizeof(void*)*14);
v_cancelTk_x3f_367_ = lean_ctor_get(v___y_351_, 12);
v_suppressElabErrors_368_ = lean_ctor_get_uint8(v___y_351_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_369_ = lean_ctor_get(v___y_351_, 13);
v___x_370_ = lean_st_ref_get(v___y_352_);
v_traceState_371_ = lean_ctor_get(v___x_370_, 4);
lean_inc_ref(v_traceState_371_);
lean_dec(v___x_370_);
v_traces_372_ = lean_ctor_get(v_traceState_371_, 0);
lean_inc_ref(v_traces_372_);
lean_dec_ref(v_traceState_371_);
v_ref_373_ = l_Lean_replaceRef(v_ref_347_, v_ref_359_);
lean_inc_ref(v_inheritedTraceOptions_369_);
lean_inc(v_cancelTk_x3f_367_);
lean_inc(v_currMacroScope_365_);
lean_inc(v_quotContext_364_);
lean_inc(v_maxHeartbeats_363_);
lean_inc(v_initHeartbeats_362_);
lean_inc(v_openDecls_361_);
lean_inc(v_currNamespace_360_);
lean_inc(v_maxRecDepth_358_);
lean_inc(v_currRecDepth_357_);
lean_inc_ref(v_options_356_);
lean_inc_ref(v_fileMap_355_);
lean_inc_ref(v_fileName_354_);
v___x_374_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_374_, 0, v_fileName_354_);
lean_ctor_set(v___x_374_, 1, v_fileMap_355_);
lean_ctor_set(v___x_374_, 2, v_options_356_);
lean_ctor_set(v___x_374_, 3, v_currRecDepth_357_);
lean_ctor_set(v___x_374_, 4, v_maxRecDepth_358_);
lean_ctor_set(v___x_374_, 5, v_ref_373_);
lean_ctor_set(v___x_374_, 6, v_currNamespace_360_);
lean_ctor_set(v___x_374_, 7, v_openDecls_361_);
lean_ctor_set(v___x_374_, 8, v_initHeartbeats_362_);
lean_ctor_set(v___x_374_, 9, v_maxHeartbeats_363_);
lean_ctor_set(v___x_374_, 10, v_quotContext_364_);
lean_ctor_set(v___x_374_, 11, v_currMacroScope_365_);
lean_ctor_set(v___x_374_, 12, v_cancelTk_x3f_367_);
lean_ctor_set(v___x_374_, 13, v_inheritedTraceOptions_369_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*14, v_diag_366_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*14 + 1, v_suppressElabErrors_368_);
v___x_375_ = l_Lean_PersistentArray_toArray___redArg(v_traces_372_);
lean_dec_ref(v_traces_372_);
v_sz_376_ = lean_array_size(v___x_375_);
v___x_377_ = ((size_t)0ULL);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__7(v_sz_376_, v___x_377_, v___x_375_);
v_msg_379_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_379_, 0, v_data_346_);
lean_ctor_set(v_msg_379_, 1, v_msg_348_);
lean_ctor_set(v_msg_379_, 2, v___x_378_);
v___x_380_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(v_msg_379_, v___y_349_, v___y_350_, v___x_374_, v___y_352_);
lean_dec_ref(v___x_374_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_418_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_418_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_418_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v_traceState_386_; lean_object* v_env_387_; lean_object* v_nextMacroScope_388_; lean_object* v_ngen_389_; lean_object* v_auxDeclNGen_390_; lean_object* v_cache_391_; lean_object* v_messages_392_; lean_object* v_infoState_393_; lean_object* v_snapshotTasks_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_417_; 
v___x_385_ = lean_st_ref_take(v___y_352_);
v_traceState_386_ = lean_ctor_get(v___x_385_, 4);
v_env_387_ = lean_ctor_get(v___x_385_, 0);
v_nextMacroScope_388_ = lean_ctor_get(v___x_385_, 1);
v_ngen_389_ = lean_ctor_get(v___x_385_, 2);
v_auxDeclNGen_390_ = lean_ctor_get(v___x_385_, 3);
v_cache_391_ = lean_ctor_get(v___x_385_, 5);
v_messages_392_ = lean_ctor_get(v___x_385_, 6);
v_infoState_393_ = lean_ctor_get(v___x_385_, 7);
v_snapshotTasks_394_ = lean_ctor_get(v___x_385_, 8);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_417_ == 0)
{
v___x_396_ = v___x_385_;
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snapshotTasks_394_);
lean_inc(v_infoState_393_);
lean_inc(v_messages_392_);
lean_inc(v_cache_391_);
lean_inc(v_traceState_386_);
lean_inc(v_auxDeclNGen_390_);
lean_inc(v_ngen_389_);
lean_inc(v_nextMacroScope_388_);
lean_inc(v_env_387_);
lean_dec(v___x_385_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint64_t v_tid_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_415_; 
v_tid_398_ = lean_ctor_get_uint64(v_traceState_386_, sizeof(void*)*1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_traceState_386_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_traceState_386_, 0);
lean_dec(v_unused_416_);
v___x_400_ = v_traceState_386_;
v_isShared_401_ = v_isSharedCheck_415_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_traceState_386_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_415_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_ref_347_);
lean_ctor_set(v___x_402_, 1, v_a_381_);
v___x_403_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_345_, v___x_402_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_403_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_403_);
lean_ctor_set_uint64(v_reuseFailAlloc_414_, sizeof(void*)*1, v_tid_398_);
v___x_405_ = v_reuseFailAlloc_414_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v___x_405_);
v___x_407_ = v___x_396_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_env_387_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_388_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_389_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_cache_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_messages_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_infoState_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_snapshotTasks_394_);
v___x_407_ = v_reuseFailAlloc_413_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_408_ = lean_st_ref_set(v___y_352_, v___x_407_);
v___x_409_ = lean_box(0);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_409_);
v___x_411_ = v___x_383_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5___boxed(lean_object* v_oldTraces_419_, lean_object* v_data_420_, lean_object* v_ref_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5(v_oldTraces_419_, v_data_420_, v_ref_421_, v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__0));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2(void){
_start:
{
lean_object* v___x_432_; double v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_float_of_nat(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__3));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5(void){
_start:
{
lean_object* v___x_437_; double v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(1000u);
v___x_438_ = lean_float_of_nat(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(lean_object* v_cls_439_, uint8_t v_collapsed_440_, lean_object* v_tag_441_, lean_object* v_opts_442_, uint8_t v_clsEnabled_443_, lean_object* v_oldTraces_444_, lean_object* v_msg_445_, lean_object* v_resStartStop_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_fst_452_; lean_object* v_snd_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_551_; 
v_fst_452_ = lean_ctor_get(v_resStartStop_446_, 0);
v_snd_453_ = lean_ctor_get(v_resStartStop_446_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_resStartStop_446_);
if (v_isSharedCheck_551_ == 0)
{
v___x_455_ = v_resStartStop_446_;
v_isShared_456_ = v_isSharedCheck_551_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_snd_453_);
lean_inc(v_fst_452_);
lean_dec(v_resStartStop_446_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_551_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v_data_460_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_550_; 
v_fst_471_ = lean_ctor_get(v_snd_453_, 0);
v_snd_472_ = lean_ctor_get(v_snd_453_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_snd_453_);
if (v_isSharedCheck_550_ == 0)
{
v___x_474_ = v_snd_453_;
v_isShared_475_ = v_isSharedCheck_550_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_inc(v_fst_471_);
lean_dec(v_snd_453_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_550_;
goto v_resetjp_473_;
}
v___jp_457_:
{
lean_object* v___x_461_; 
lean_inc(v___y_458_);
v___x_461_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5(v_oldTraces_444_, v_data_460_, v___y_458_, v___y_459_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; 
lean_dec_ref(v___x_461_);
v___x_462_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_fst_452_);
return v___x_462_;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_fst_452_);
v_a_463_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_461_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
v_resetjp_473_:
{
lean_object* v___x_476_; uint8_t v___x_477_; lean_object* v___y_479_; lean_object* v_a_480_; uint8_t v___y_504_; double v___y_535_; 
v___x_476_ = l_Lean_trace_profiler;
v___x_477_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_opts_442_, v___x_476_);
if (v___x_477_ == 0)
{
v___y_504_ = v___x_477_;
goto v___jp_503_;
}
else
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = l_Lean_trace_profiler_useHeartbeats;
v___x_541_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_opts_442_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; double v___x_544_; double v___x_545_; double v___x_546_; 
v___x_542_ = l_Lean_trace_profiler_threshold;
v___x_543_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(v_opts_442_, v___x_542_);
v___x_544_ = lean_float_of_nat(v___x_543_);
v___x_545_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__5);
v___x_546_ = lean_float_div(v___x_544_, v___x_545_);
v___y_535_ = v___x_546_;
goto v___jp_534_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; double v___x_549_; 
v___x_547_ = l_Lean_trace_profiler_threshold;
v___x_548_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__7(v_opts_442_, v___x_547_);
v___x_549_ = lean_float_of_nat(v___x_548_);
v___y_535_ = v___x_549_;
goto v___jp_534_;
}
}
v___jp_478_:
{
uint8_t v_result_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v_result_481_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__4(v_fst_452_);
v___x_482_ = l_Lean_TraceResult_toEmoji(v_result_481_);
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
v___x_484_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__1);
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 7);
lean_ctor_set(v___x_474_, 1, v___x_484_);
lean_ctor_set(v___x_474_, 0, v___x_483_);
v___x_486_ = v___x_474_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_497_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v_m_488_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 7);
lean_ctor_set(v___x_455_, 1, v_a_480_);
lean_ctor_set(v___x_455_, 0, v___x_486_);
v_m_488_ = v___x_455_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_a_480_);
v_m_488_ = v_reuseFailAlloc_496_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; double v___x_491_; lean_object* v_data_492_; 
v___x_489_ = lean_box(v_result_481_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
v___x_491_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__2);
lean_inc_ref(v_tag_441_);
lean_inc_ref(v___x_490_);
lean_inc(v_cls_439_);
v_data_492_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_492_, 0, v_cls_439_);
lean_ctor_set(v_data_492_, 1, v___x_490_);
lean_ctor_set(v_data_492_, 2, v_tag_441_);
lean_ctor_set_float(v_data_492_, sizeof(void*)*3, v___x_491_);
lean_ctor_set_float(v_data_492_, sizeof(void*)*3 + 8, v___x_491_);
lean_ctor_set_uint8(v_data_492_, sizeof(void*)*3 + 16, v_collapsed_440_);
if (v___x_477_ == 0)
{
lean_dec_ref(v___x_490_);
lean_dec(v_snd_472_);
lean_dec(v_fst_471_);
lean_dec_ref(v_tag_441_);
lean_dec(v_cls_439_);
v___y_458_ = v___y_479_;
v___y_459_ = v_m_488_;
v_data_460_ = v_data_492_;
goto v___jp_457_;
}
else
{
lean_object* v_data_493_; double v___x_494_; double v___x_495_; 
lean_dec_ref(v_data_492_);
v_data_493_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_493_, 0, v_cls_439_);
lean_ctor_set(v_data_493_, 1, v___x_490_);
lean_ctor_set(v_data_493_, 2, v_tag_441_);
v___x_494_ = lean_unbox_float(v_fst_471_);
lean_dec(v_fst_471_);
lean_ctor_set_float(v_data_493_, sizeof(void*)*3, v___x_494_);
v___x_495_ = lean_unbox_float(v_snd_472_);
lean_dec(v_snd_472_);
lean_ctor_set_float(v_data_493_, sizeof(void*)*3 + 8, v___x_495_);
lean_ctor_set_uint8(v_data_493_, sizeof(void*)*3 + 16, v_collapsed_440_);
v___y_458_ = v___y_479_;
v___y_459_ = v_m_488_;
v_data_460_ = v_data_493_;
goto v___jp_457_;
}
}
}
}
v___jp_498_:
{
lean_object* v_ref_499_; lean_object* v___x_500_; 
v_ref_499_ = lean_ctor_get(v___y_449_, 5);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc(v_fst_452_);
v___x_500_ = lean_apply_6(v_msg_445_, v_fst_452_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, lean_box(0));
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___y_479_ = v_ref_499_;
v_a_480_ = v_a_501_;
goto v___jp_478_;
}
else
{
lean_object* v___x_502_; 
lean_dec_ref(v___x_500_);
v___x_502_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___closed__4);
v___y_479_ = v_ref_499_;
v_a_480_ = v___x_502_;
goto v___jp_478_;
}
}
v___jp_503_:
{
if (v_clsEnabled_443_ == 0)
{
if (v___y_504_ == 0)
{
lean_object* v___x_505_; lean_object* v_traceState_506_; lean_object* v_env_507_; lean_object* v_nextMacroScope_508_; lean_object* v_ngen_509_; lean_object* v_auxDeclNGen_510_; lean_object* v_cache_511_; lean_object* v_messages_512_; lean_object* v_infoState_513_; lean_object* v_snapshotTasks_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_533_; 
lean_del_object(v___x_474_);
lean_dec(v_snd_472_);
lean_dec(v_fst_471_);
lean_del_object(v___x_455_);
lean_dec_ref(v_msg_445_);
lean_dec_ref(v_tag_441_);
lean_dec(v_cls_439_);
v___x_505_ = lean_st_ref_take(v___y_450_);
v_traceState_506_ = lean_ctor_get(v___x_505_, 4);
v_env_507_ = lean_ctor_get(v___x_505_, 0);
v_nextMacroScope_508_ = lean_ctor_get(v___x_505_, 1);
v_ngen_509_ = lean_ctor_get(v___x_505_, 2);
v_auxDeclNGen_510_ = lean_ctor_get(v___x_505_, 3);
v_cache_511_ = lean_ctor_get(v___x_505_, 5);
v_messages_512_ = lean_ctor_get(v___x_505_, 6);
v_infoState_513_ = lean_ctor_get(v___x_505_, 7);
v_snapshotTasks_514_ = lean_ctor_get(v___x_505_, 8);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_533_ == 0)
{
v___x_516_ = v___x_505_;
v_isShared_517_ = v_isSharedCheck_533_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snapshotTasks_514_);
lean_inc(v_infoState_513_);
lean_inc(v_messages_512_);
lean_inc(v_cache_511_);
lean_inc(v_traceState_506_);
lean_inc(v_auxDeclNGen_510_);
lean_inc(v_ngen_509_);
lean_inc(v_nextMacroScope_508_);
lean_inc(v_env_507_);
lean_dec(v___x_505_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_533_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint64_t v_tid_518_; lean_object* v_traces_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_532_; 
v_tid_518_ = lean_ctor_get_uint64(v_traceState_506_, sizeof(void*)*1);
v_traces_519_ = lean_ctor_get(v_traceState_506_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_traceState_506_);
if (v_isSharedCheck_532_ == 0)
{
v___x_521_ = v_traceState_506_;
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_traces_519_);
lean_dec(v_traceState_506_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_444_, v_traces_519_);
lean_dec_ref(v_traces_519_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_523_);
lean_ctor_set_uint64(v_reuseFailAlloc_531_, sizeof(void*)*1, v_tid_518_);
v___x_525_ = v_reuseFailAlloc_531_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v___x_525_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_env_507_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_nextMacroScope_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_ngen_509_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_auxDeclNGen_510_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_530_, 5, v_cache_511_);
lean_ctor_set(v_reuseFailAlloc_530_, 6, v_messages_512_);
lean_ctor_set(v_reuseFailAlloc_530_, 7, v_infoState_513_);
lean_ctor_set(v_reuseFailAlloc_530_, 8, v_snapshotTasks_514_);
v___x_527_ = v_reuseFailAlloc_530_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_st_ref_set(v___y_450_, v___x_527_);
v___x_529_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_fst_452_);
return v___x_529_;
}
}
}
}
}
else
{
goto v___jp_498_;
}
}
else
{
goto v___jp_498_;
}
}
v___jp_534_:
{
double v___x_536_; double v___x_537_; double v___x_538_; uint8_t v___x_539_; 
v___x_536_ = lean_unbox_float(v_snd_472_);
v___x_537_ = lean_unbox_float(v_fst_471_);
v___x_538_ = lean_float_sub(v___x_536_, v___x_537_);
v___x_539_ = lean_float_decLt(v___y_535_, v___x_538_);
v___y_504_ = v___x_539_;
goto v___jp_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4___boxed(lean_object* v_cls_552_, lean_object* v_collapsed_553_, lean_object* v_tag_554_, lean_object* v_opts_555_, lean_object* v_clsEnabled_556_, lean_object* v_oldTraces_557_, lean_object* v_msg_558_, lean_object* v_resStartStop_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_collapsed_boxed_565_; uint8_t v_clsEnabled_boxed_566_; lean_object* v_res_567_; 
v_collapsed_boxed_565_ = lean_unbox(v_collapsed_553_);
v_clsEnabled_boxed_566_ = lean_unbox(v_clsEnabled_556_);
v_res_567_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v_cls_552_, v_collapsed_boxed_565_, v_tag_554_, v_opts_555_, v_clsEnabled_boxed_566_, v_oldTraces_557_, v_msg_558_, v_resStartStop_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec_ref(v_opts_555_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(uint8_t v___x_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_x_570_);
return v___x_576_;
}
else
{
lean_object* v_head_577_; lean_object* v_tail_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_head_577_ = lean_ctor_get(v_x_569_, 0);
v_tail_578_ = lean_ctor_get(v_x_569_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_601_ == 0)
{
v___x_580_ = v_x_569_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_tail_578_);
lean_inc(v_head_577_);
lean_dec(v_x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; 
lean_inc(v_head_577_);
v___x_582_ = l_Lean_MVarId_inferInstance(v_head_577_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_dec_ref(v___x_582_);
lean_del_object(v___x_580_);
lean_dec(v_head_577_);
v_x_569_ = v_tail_578_;
goto _start;
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_600_; 
v_a_584_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_600_ == 0)
{
v___x_586_ = v___x_582_;
v_isShared_587_ = v_isSharedCheck_600_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_600_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint8_t v___y_589_; uint8_t v___x_598_; 
v___x_598_ = l_Lean_Exception_isInterrupt(v_a_584_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
lean_inc(v_a_584_);
v___x_599_ = l_Lean_Exception_isRuntime(v_a_584_);
v___y_589_ = v___x_599_;
goto v___jp_588_;
}
else
{
v___y_589_ = v___x_598_;
goto v___jp_588_;
}
v___jp_588_:
{
if (v___y_589_ == 0)
{
lean_del_object(v___x_586_);
lean_dec(v_a_584_);
if (v___x_568_ == 0)
{
lean_del_object(v___x_580_);
lean_dec(v_head_577_);
v_x_569_ = v_tail_578_;
goto _start;
}
else
{
lean_object* v___x_592_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_x_570_);
v___x_592_ = v___x_580_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_head_577_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_x_570_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v_x_569_ = v_tail_578_;
v_x_570_ = v___x_592_;
goto _start;
}
}
}
else
{
lean_object* v___x_596_; 
lean_del_object(v___x_580_);
lean_dec(v_tail_578_);
lean_dec(v_head_577_);
lean_dec(v_x_570_);
if (v_isShared_587_ == 0)
{
v___x_596_ = v___x_586_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_584_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6___boxed(lean_object* v___x_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v___x_14041__boxed_610_; lean_object* v_res_611_; 
v___x_14041__boxed_610_ = lean_unbox(v___x_602_);
v_res_611_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v___x_14041__boxed_610_, v_x_603_, v_x_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(uint8_t v___x_612_, uint8_t v___x_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_x_615_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_647_; 
v_head_622_ = lean_ctor_get(v_x_614_, 0);
v_tail_623_ = lean_ctor_get(v_x_614_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_614_);
if (v_isSharedCheck_647_ == 0)
{
v___x_625_ = v_x_614_;
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tail_623_);
lean_inc(v_head_622_);
lean_dec(v_x_614_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v_a_628_; lean_object* v___x_634_; 
lean_inc(v_head_622_);
v___x_634_ = l_Lean_MVarId_inferInstance(v_head_622_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref(v___x_634_);
v_a_628_ = v___x_612_;
goto v___jp_627_;
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_646_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_646_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_646_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_646_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v___y_640_; uint8_t v___x_644_; 
v___x_644_ = l_Lean_Exception_isInterrupt(v_a_635_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
lean_inc(v_a_635_);
v___x_645_ = l_Lean_Exception_isRuntime(v_a_635_);
v___y_640_ = v___x_645_;
goto v___jp_639_;
}
else
{
v___y_640_ = v___x_644_;
goto v___jp_639_;
}
v___jp_639_:
{
if (v___y_640_ == 0)
{
lean_del_object(v___x_637_);
lean_dec(v_a_635_);
v_a_628_ = v___x_613_;
goto v___jp_627_;
}
else
{
lean_object* v___x_642_; 
lean_del_object(v___x_625_);
lean_dec(v_tail_623_);
lean_dec(v_head_622_);
lean_dec(v_x_615_);
if (v_isShared_638_ == 0)
{
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_635_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
v___jp_627_:
{
if (v_a_628_ == 0)
{
lean_del_object(v___x_625_);
lean_dec(v_head_622_);
v_x_614_ = v_tail_623_;
goto _start;
}
else
{
lean_object* v___x_631_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_x_615_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_head_622_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_x_615_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v_x_614_ = v_tail_623_;
v_x_615_ = v___x_631_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5___boxed(lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_14118__boxed_657_; uint8_t v___x_14119__boxed_658_; lean_object* v_res_659_; 
v___x_14118__boxed_657_ = lean_unbox(v___x_648_);
v___x_14119__boxed_658_ = lean_unbox(v___x_649_);
v_res_659_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_14118__boxed_657_, v___x_14119__boxed_658_, v_x_650_, v_x_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(uint8_t v___x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_x_662_);
return v___x_668_;
}
else
{
lean_object* v_head_669_; lean_object* v_tail_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_693_; 
v_head_669_ = lean_ctor_get(v_x_661_, 0);
v_tail_670_ = lean_ctor_get(v_x_661_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_661_);
if (v_isSharedCheck_693_ == 0)
{
v___x_672_ = v_x_661_;
v_isShared_673_ = v_isSharedCheck_693_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_tail_670_);
lean_inc(v_head_669_);
lean_dec(v_x_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_693_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_679_; 
lean_inc(v_head_669_);
v___x_679_ = l_Lean_MVarId_inferInstance(v_head_669_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec_ref(v___x_679_);
if (v___x_660_ == 0)
{
lean_del_object(v___x_672_);
lean_dec(v_head_669_);
v_x_661_ = v_tail_670_;
goto _start;
}
else
{
goto v___jp_674_;
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_692_; 
v_a_681_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_692_ == 0)
{
v___x_683_ = v___x_679_;
v_isShared_684_ = v_isSharedCheck_692_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_692_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___y_686_; uint8_t v___x_690_; 
v___x_690_ = l_Lean_Exception_isInterrupt(v_a_681_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
lean_inc(v_a_681_);
v___x_691_ = l_Lean_Exception_isRuntime(v_a_681_);
v___y_686_ = v___x_691_;
goto v___jp_685_;
}
else
{
v___y_686_ = v___x_690_;
goto v___jp_685_;
}
v___jp_685_:
{
if (v___y_686_ == 0)
{
lean_del_object(v___x_683_);
lean_dec(v_a_681_);
goto v___jp_674_;
}
else
{
lean_object* v___x_688_; 
lean_del_object(v___x_672_);
lean_dec(v_tail_670_);
lean_dec(v_head_669_);
lean_dec(v_x_662_);
if (v_isShared_684_ == 0)
{
v___x_688_ = v___x_683_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_681_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
v___jp_674_:
{
lean_object* v___x_676_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_x_662_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_head_669_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_x_662_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v_x_661_ = v_tail_670_;
v_x_662_ = v___x_676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0___boxed(lean_object* v___x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_14200__boxed_702_; lean_object* v_res_703_; 
v___x_14200__boxed_702_ = lean_unbox(v___x_694_);
v_res_703_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v___x_14200__boxed_702_, v_x_695_, v_x_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_703_;
}
}
static double _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_704_; double v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(1000000000u);
v___x_705_ = lean_float_of_nat(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(uint8_t v_transparency_706_, lean_object* v_g_707_, lean_object* v_e_708_, lean_object* v_cfg_709_, lean_object* v___x_710_, lean_object* v___x_711_, uint8_t v___x_712_, lean_object* v___x_713_, lean_object* v___f_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_options_720_; uint8_t v_hasTrace_721_; 
v_options_720_ = lean_ctor_get(v___y_717_, 2);
v_hasTrace_721_ = lean_ctor_get_uint8(v_options_720_, sizeof(void*)*1);
if (v_hasTrace_721_ == 0)
{
lean_object* v___x_722_; uint8_t v_foApprox_723_; uint8_t v_ctxApprox_724_; uint8_t v_quasiPatternApprox_725_; uint8_t v_constApprox_726_; uint8_t v_isDefEqStuckEx_727_; uint8_t v_unificationHints_728_; uint8_t v_proofIrrelevance_729_; uint8_t v_assignSyntheticOpaque_730_; uint8_t v_offsetCnstrs_731_; uint8_t v_etaStruct_732_; uint8_t v_univApprox_733_; uint8_t v_iota_734_; uint8_t v_beta_735_; uint8_t v_proj_736_; uint8_t v_zeta_737_; uint8_t v_zetaDelta_738_; uint8_t v_zetaUnused_739_; uint8_t v_zetaHave_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___f_714_);
lean_dec_ref(v___x_713_);
lean_dec(v___x_711_);
v___x_722_ = l_Lean_Meta_Context_config(v___y_715_);
v_foApprox_723_ = lean_ctor_get_uint8(v___x_722_, 0);
v_ctxApprox_724_ = lean_ctor_get_uint8(v___x_722_, 1);
v_quasiPatternApprox_725_ = lean_ctor_get_uint8(v___x_722_, 2);
v_constApprox_726_ = lean_ctor_get_uint8(v___x_722_, 3);
v_isDefEqStuckEx_727_ = lean_ctor_get_uint8(v___x_722_, 4);
v_unificationHints_728_ = lean_ctor_get_uint8(v___x_722_, 5);
v_proofIrrelevance_729_ = lean_ctor_get_uint8(v___x_722_, 6);
v_assignSyntheticOpaque_730_ = lean_ctor_get_uint8(v___x_722_, 7);
v_offsetCnstrs_731_ = lean_ctor_get_uint8(v___x_722_, 8);
v_etaStruct_732_ = lean_ctor_get_uint8(v___x_722_, 10);
v_univApprox_733_ = lean_ctor_get_uint8(v___x_722_, 11);
v_iota_734_ = lean_ctor_get_uint8(v___x_722_, 12);
v_beta_735_ = lean_ctor_get_uint8(v___x_722_, 13);
v_proj_736_ = lean_ctor_get_uint8(v___x_722_, 14);
v_zeta_737_ = lean_ctor_get_uint8(v___x_722_, 15);
v_zetaDelta_738_ = lean_ctor_get_uint8(v___x_722_, 16);
v_zetaUnused_739_ = lean_ctor_get_uint8(v___x_722_, 17);
v_zetaHave_740_ = lean_ctor_get_uint8(v___x_722_, 18);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_778_ == 0)
{
v___x_742_ = v___x_722_;
v_isShared_743_ = v_isSharedCheck_778_;
goto v_resetjp_741_;
}
else
{
lean_dec(v___x_722_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_778_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint8_t v_trackZetaDelta_744_; lean_object* v_zetaDeltaSet_745_; lean_object* v_lctx_746_; lean_object* v_localInstances_747_; lean_object* v_defEqCtx_x3f_748_; lean_object* v_synthPendingDepth_749_; lean_object* v_canUnfold_x3f_750_; uint8_t v_univApprox_751_; uint8_t v_inTypeClassResolution_752_; uint8_t v_cacheInferType_753_; lean_object* v_config_755_; 
v_trackZetaDelta_744_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7);
v_zetaDeltaSet_745_ = lean_ctor_get(v___y_715_, 1);
v_lctx_746_ = lean_ctor_get(v___y_715_, 2);
v_localInstances_747_ = lean_ctor_get(v___y_715_, 3);
v_defEqCtx_x3f_748_ = lean_ctor_get(v___y_715_, 4);
v_synthPendingDepth_749_ = lean_ctor_get(v___y_715_, 5);
v_canUnfold_x3f_750_ = lean_ctor_get(v___y_715_, 6);
v_univApprox_751_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_752_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 2);
v_cacheInferType_753_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 3);
if (v_isShared_743_ == 0)
{
v_config_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 0, v_foApprox_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 1, v_ctxApprox_724_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 2, v_quasiPatternApprox_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 3, v_constApprox_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 4, v_isDefEqStuckEx_727_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 5, v_unificationHints_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 6, v_proofIrrelevance_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 7, v_assignSyntheticOpaque_730_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 8, v_offsetCnstrs_731_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 10, v_etaStruct_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 11, v_univApprox_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 12, v_iota_734_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 13, v_beta_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 14, v_proj_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 15, v_zeta_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 16, v_zetaDelta_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 17, v_zetaUnused_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, 18, v_zetaHave_740_);
v_config_755_ = v_reuseFailAlloc_777_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v___x_759_; uint64_t v___x_760_; uint64_t v_key_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_ctor_set_uint8(v_config_755_, 9, v_transparency_706_);
v___x_756_ = l_Lean_Meta_Context_configKey(v___y_715_);
v___x_757_ = 2ULL;
v___x_758_ = lean_uint64_shift_right(v___x_756_, v___x_757_);
v___x_759_ = lean_uint64_shift_left(v___x_758_, v___x_757_);
v___x_760_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_706_);
v_key_761_ = lean_uint64_lor(v___x_759_, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_762_, 0, v_config_755_);
lean_ctor_set_uint64(v___x_762_, sizeof(void*)*1, v_key_761_);
lean_inc(v_canUnfold_x3f_750_);
lean_inc(v_synthPendingDepth_749_);
lean_inc(v_defEqCtx_x3f_748_);
lean_inc_ref(v_localInstances_747_);
lean_inc_ref(v_lctx_746_);
lean_inc(v_zetaDeltaSet_745_);
v___x_763_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_zetaDeltaSet_745_);
lean_ctor_set(v___x_763_, 2, v_lctx_746_);
lean_ctor_set(v___x_763_, 3, v_localInstances_747_);
lean_ctor_set(v___x_763_, 4, v_defEqCtx_x3f_748_);
lean_ctor_set(v___x_763_, 5, v_synthPendingDepth_749_);
lean_ctor_set(v___x_763_, 6, v_canUnfold_x3f_750_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*7, v_trackZetaDelta_744_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*7 + 1, v_univApprox_751_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*7 + 2, v_inTypeClassResolution_752_);
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*7 + 3, v_cacheInferType_753_);
v___x_764_ = l_Lean_MVarId_apply(v_g_707_, v_e_708_, v_cfg_709_, v___x_710_, v___x_763_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v___x_763_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
v___x_766_ = lean_box(0);
v___x_767_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__0(v_hasTrace_721_, v_a_765_, v___x_766_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_776_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_776_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_776_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = l_List_reverse___redArg(v_a_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_772_);
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
return v___x_767_;
}
}
else
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_1018_; 
lean_inc(v___x_711_);
v___x_779_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(v___x_711_, v___y_717_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_1018_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_1018_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v_a_787_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v_a_803_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v_a_823_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v_a_836_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; uint8_t v___x_958_; 
v___x_958_ = lean_unbox(v_a_780_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = l_Lean_trace_profiler;
v___x_960_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_options_720_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; uint8_t v_foApprox_962_; uint8_t v_ctxApprox_963_; uint8_t v_quasiPatternApprox_964_; uint8_t v_constApprox_965_; uint8_t v_isDefEqStuckEx_966_; uint8_t v_unificationHints_967_; uint8_t v_proofIrrelevance_968_; uint8_t v_assignSyntheticOpaque_969_; uint8_t v_offsetCnstrs_970_; uint8_t v_etaStruct_971_; uint8_t v_univApprox_972_; uint8_t v_iota_973_; uint8_t v_beta_974_; uint8_t v_proj_975_; uint8_t v_zeta_976_; uint8_t v_zetaDelta_977_; uint8_t v_zetaUnused_978_; uint8_t v_zetaHave_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1017_; 
lean_del_object(v___x_782_);
lean_dec(v_a_780_);
lean_dec_ref(v___f_714_);
lean_dec_ref(v___x_713_);
lean_dec(v___x_711_);
v___x_961_ = l_Lean_Meta_Context_config(v___y_715_);
v_foApprox_962_ = lean_ctor_get_uint8(v___x_961_, 0);
v_ctxApprox_963_ = lean_ctor_get_uint8(v___x_961_, 1);
v_quasiPatternApprox_964_ = lean_ctor_get_uint8(v___x_961_, 2);
v_constApprox_965_ = lean_ctor_get_uint8(v___x_961_, 3);
v_isDefEqStuckEx_966_ = lean_ctor_get_uint8(v___x_961_, 4);
v_unificationHints_967_ = lean_ctor_get_uint8(v___x_961_, 5);
v_proofIrrelevance_968_ = lean_ctor_get_uint8(v___x_961_, 6);
v_assignSyntheticOpaque_969_ = lean_ctor_get_uint8(v___x_961_, 7);
v_offsetCnstrs_970_ = lean_ctor_get_uint8(v___x_961_, 8);
v_etaStruct_971_ = lean_ctor_get_uint8(v___x_961_, 10);
v_univApprox_972_ = lean_ctor_get_uint8(v___x_961_, 11);
v_iota_973_ = lean_ctor_get_uint8(v___x_961_, 12);
v_beta_974_ = lean_ctor_get_uint8(v___x_961_, 13);
v_proj_975_ = lean_ctor_get_uint8(v___x_961_, 14);
v_zeta_976_ = lean_ctor_get_uint8(v___x_961_, 15);
v_zetaDelta_977_ = lean_ctor_get_uint8(v___x_961_, 16);
v_zetaUnused_978_ = lean_ctor_get_uint8(v___x_961_, 17);
v_zetaHave_979_ = lean_ctor_get_uint8(v___x_961_, 18);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_981_ = v___x_961_;
v_isShared_982_ = v_isSharedCheck_1017_;
goto v_resetjp_980_;
}
else
{
lean_dec(v___x_961_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1017_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
uint8_t v_trackZetaDelta_983_; lean_object* v_zetaDeltaSet_984_; lean_object* v_lctx_985_; lean_object* v_localInstances_986_; lean_object* v_defEqCtx_x3f_987_; lean_object* v_synthPendingDepth_988_; lean_object* v_canUnfold_x3f_989_; uint8_t v_univApprox_990_; uint8_t v_inTypeClassResolution_991_; uint8_t v_cacheInferType_992_; lean_object* v_config_994_; 
v_trackZetaDelta_983_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7);
v_zetaDeltaSet_984_ = lean_ctor_get(v___y_715_, 1);
v_lctx_985_ = lean_ctor_get(v___y_715_, 2);
v_localInstances_986_ = lean_ctor_get(v___y_715_, 3);
v_defEqCtx_x3f_987_ = lean_ctor_get(v___y_715_, 4);
v_synthPendingDepth_988_ = lean_ctor_get(v___y_715_, 5);
v_canUnfold_x3f_989_ = lean_ctor_get(v___y_715_, 6);
v_univApprox_990_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_991_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 2);
v_cacheInferType_992_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 3);
if (v_isShared_982_ == 0)
{
v_config_994_ = v___x_981_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 0, v_foApprox_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 1, v_ctxApprox_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 2, v_quasiPatternApprox_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 3, v_constApprox_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 4, v_isDefEqStuckEx_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 5, v_unificationHints_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 6, v_proofIrrelevance_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 7, v_assignSyntheticOpaque_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 8, v_offsetCnstrs_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 10, v_etaStruct_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 11, v_univApprox_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 12, v_iota_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 13, v_beta_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 14, v_proj_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 15, v_zeta_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 16, v_zetaDelta_977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 17, v_zetaUnused_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, 18, v_zetaHave_979_);
v_config_994_ = v_reuseFailAlloc_1016_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
uint64_t v___x_995_; uint64_t v___x_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v___x_999_; uint64_t v_key_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_ctor_set_uint8(v_config_994_, 9, v_transparency_706_);
v___x_995_ = l_Lean_Meta_Context_configKey(v___y_715_);
v___x_996_ = 2ULL;
v___x_997_ = lean_uint64_shift_right(v___x_995_, v___x_996_);
v___x_998_ = lean_uint64_shift_left(v___x_997_, v___x_996_);
v___x_999_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_706_);
v_key_1000_ = lean_uint64_lor(v___x_998_, v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1001_, 0, v_config_994_);
lean_ctor_set_uint64(v___x_1001_, sizeof(void*)*1, v_key_1000_);
lean_inc(v_canUnfold_x3f_989_);
lean_inc(v_synthPendingDepth_988_);
lean_inc(v_defEqCtx_x3f_987_);
lean_inc_ref(v_localInstances_986_);
lean_inc_ref(v_lctx_985_);
lean_inc(v_zetaDeltaSet_984_);
v___x_1002_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_zetaDeltaSet_984_);
lean_ctor_set(v___x_1002_, 2, v_lctx_985_);
lean_ctor_set(v___x_1002_, 3, v_localInstances_986_);
lean_ctor_set(v___x_1002_, 4, v_defEqCtx_x3f_987_);
lean_ctor_set(v___x_1002_, 5, v_synthPendingDepth_988_);
lean_ctor_set(v___x_1002_, 6, v_canUnfold_x3f_989_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*7, v_trackZetaDelta_983_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*7 + 1, v_univApprox_990_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*7 + 2, v_inTypeClassResolution_991_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*7 + 3, v_cacheInferType_992_);
v___x_1003_ = l_Lean_MVarId_apply(v_g_707_, v_e_708_, v_cfg_709_, v___x_710_, v___x_1002_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = lean_box(0);
v___x_1006_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_960_, v_hasTrace_721_, v_a_1004_, v___x_1005_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = l_List_reverse___redArg(v_a_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
return v___x_1006_;
}
}
else
{
return v___x_1003_;
}
}
}
}
else
{
goto v___jp_851_;
}
}
else
{
goto v___jp_851_;
}
v___jp_784_:
{
lean_object* v___x_788_; double v___x_789_; double v___x_790_; double v___x_791_; double v___x_792_; double v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; 
v___x_788_ = lean_io_mono_nanos_now();
v___x_789_ = lean_float_of_nat(v___y_786_);
v___x_790_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0);
v___x_791_ = lean_float_div(v___x_789_, v___x_790_);
v___x_792_ = lean_float_of_nat(v___x_788_);
v___x_793_ = lean_float_div(v___x_792_, v___x_790_);
v___x_794_ = lean_box_float(v___x_791_);
v___x_795_ = lean_box_float(v___x_793_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_a_787_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_unbox(v_a_780_);
lean_dec(v_a_780_);
v___x_799_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_711_, v___x_712_, v___x_713_, v_options_720_, v___x_798_, v___y_785_, v___f_714_, v___x_797_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_799_;
}
v___jp_800_:
{
lean_object* v___x_805_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 1);
lean_ctor_set(v___x_782_, 0, v_a_803_);
v___x_805_ = v___x_782_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v___y_785_ = v___y_801_;
v___y_786_ = v___y_802_;
v_a_787_ = v___x_805_;
goto v___jp_784_;
}
}
v___jp_807_:
{
if (lean_obj_tag(v___y_810_) == 0)
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v___y_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref(v___y_810_);
v___y_801_ = v___y_808_;
v___y_802_ = v___y_809_;
v_a_803_ = v_a_811_;
goto v___jp_800_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_782_);
v_a_812_ = lean_ctor_get(v___y_810_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___y_810_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___y_810_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___y_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_785_ = v___y_808_;
v___y_786_ = v___y_809_;
v_a_787_ = v___x_817_;
goto v___jp_784_;
}
}
}
}
v___jp_820_:
{
lean_object* v___x_824_; double v___x_825_; double v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; 
v___x_824_ = lean_io_get_num_heartbeats();
v___x_825_ = lean_float_of_nat(v___y_821_);
v___x_826_ = lean_float_of_nat(v___x_824_);
v___x_827_ = lean_box_float(v___x_825_);
v___x_828_ = lean_box_float(v___x_826_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_a_823_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_unbox(v_a_780_);
lean_dec(v_a_780_);
v___x_832_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___x_711_, v___x_712_, v___x_713_, v_options_720_, v___x_831_, v___y_822_, v___f_714_, v___x_830_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_832_;
}
v___jp_833_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_a_836_);
v___y_821_ = v___y_834_;
v___y_822_ = v___y_835_;
v_a_823_ = v___x_837_;
goto v___jp_820_;
}
v___jp_838_:
{
if (lean_obj_tag(v___y_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___y_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___y_841_);
v___y_834_ = v___y_839_;
v___y_835_ = v___y_840_;
v_a_836_ = v_a_842_;
goto v___jp_833_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___y_841_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___y_841_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___y_841_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___y_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v___y_821_ = v___y_839_;
v___y_822_ = v___y_840_;
v_a_823_ = v___x_848_;
goto v___jp_820_;
}
}
}
}
v___jp_851_:
{
lean_object* v___x_852_; lean_object* v_a_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_852_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(v___y_718_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
v___x_854_ = l_Lean_trace_profiler_useHeartbeats;
v___x_855_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_options_720_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v_foApprox_858_; uint8_t v_ctxApprox_859_; uint8_t v_quasiPatternApprox_860_; uint8_t v_constApprox_861_; uint8_t v_isDefEqStuckEx_862_; uint8_t v_unificationHints_863_; uint8_t v_proofIrrelevance_864_; uint8_t v_assignSyntheticOpaque_865_; uint8_t v_offsetCnstrs_866_; uint8_t v_etaStruct_867_; uint8_t v_univApprox_868_; uint8_t v_iota_869_; uint8_t v_beta_870_; uint8_t v_proj_871_; uint8_t v_zeta_872_; uint8_t v_zetaDelta_873_; uint8_t v_zetaUnused_874_; uint8_t v_zetaHave_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_906_; 
v___x_856_ = lean_io_mono_nanos_now();
v___x_857_ = l_Lean_Meta_Context_config(v___y_715_);
v_foApprox_858_ = lean_ctor_get_uint8(v___x_857_, 0);
v_ctxApprox_859_ = lean_ctor_get_uint8(v___x_857_, 1);
v_quasiPatternApprox_860_ = lean_ctor_get_uint8(v___x_857_, 2);
v_constApprox_861_ = lean_ctor_get_uint8(v___x_857_, 3);
v_isDefEqStuckEx_862_ = lean_ctor_get_uint8(v___x_857_, 4);
v_unificationHints_863_ = lean_ctor_get_uint8(v___x_857_, 5);
v_proofIrrelevance_864_ = lean_ctor_get_uint8(v___x_857_, 6);
v_assignSyntheticOpaque_865_ = lean_ctor_get_uint8(v___x_857_, 7);
v_offsetCnstrs_866_ = lean_ctor_get_uint8(v___x_857_, 8);
v_etaStruct_867_ = lean_ctor_get_uint8(v___x_857_, 10);
v_univApprox_868_ = lean_ctor_get_uint8(v___x_857_, 11);
v_iota_869_ = lean_ctor_get_uint8(v___x_857_, 12);
v_beta_870_ = lean_ctor_get_uint8(v___x_857_, 13);
v_proj_871_ = lean_ctor_get_uint8(v___x_857_, 14);
v_zeta_872_ = lean_ctor_get_uint8(v___x_857_, 15);
v_zetaDelta_873_ = lean_ctor_get_uint8(v___x_857_, 16);
v_zetaUnused_874_ = lean_ctor_get_uint8(v___x_857_, 17);
v_zetaHave_875_ = lean_ctor_get_uint8(v___x_857_, 18);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_906_ == 0)
{
v___x_877_ = v___x_857_;
v_isShared_878_ = v_isSharedCheck_906_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_857_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_906_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v_trackZetaDelta_879_; lean_object* v_zetaDeltaSet_880_; lean_object* v_lctx_881_; lean_object* v_localInstances_882_; lean_object* v_defEqCtx_x3f_883_; lean_object* v_synthPendingDepth_884_; lean_object* v_canUnfold_x3f_885_; uint8_t v_univApprox_886_; uint8_t v_inTypeClassResolution_887_; uint8_t v_cacheInferType_888_; lean_object* v_config_890_; 
v_trackZetaDelta_879_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7);
v_zetaDeltaSet_880_ = lean_ctor_get(v___y_715_, 1);
v_lctx_881_ = lean_ctor_get(v___y_715_, 2);
v_localInstances_882_ = lean_ctor_get(v___y_715_, 3);
v_defEqCtx_x3f_883_ = lean_ctor_get(v___y_715_, 4);
v_synthPendingDepth_884_ = lean_ctor_get(v___y_715_, 5);
v_canUnfold_x3f_885_ = lean_ctor_get(v___y_715_, 6);
v_univApprox_886_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_887_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 2);
v_cacheInferType_888_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 3);
if (v_isShared_878_ == 0)
{
v_config_890_ = v___x_877_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 0, v_foApprox_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 1, v_ctxApprox_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 2, v_quasiPatternApprox_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 3, v_constApprox_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 4, v_isDefEqStuckEx_862_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 5, v_unificationHints_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 6, v_proofIrrelevance_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 7, v_assignSyntheticOpaque_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 8, v_offsetCnstrs_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 10, v_etaStruct_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 11, v_univApprox_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 12, v_iota_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 13, v_beta_870_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 14, v_proj_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 15, v_zeta_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 16, v_zetaDelta_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 17, v_zetaUnused_874_);
lean_ctor_set_uint8(v_reuseFailAlloc_905_, 18, v_zetaHave_875_);
v_config_890_ = v_reuseFailAlloc_905_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v_key_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_ctor_set_uint8(v_config_890_, 9, v_transparency_706_);
v___x_891_ = l_Lean_Meta_Context_configKey(v___y_715_);
v___x_892_ = 2ULL;
v___x_893_ = lean_uint64_shift_right(v___x_891_, v___x_892_);
v___x_894_ = lean_uint64_shift_left(v___x_893_, v___x_892_);
v___x_895_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_706_);
v_key_896_ = lean_uint64_lor(v___x_894_, v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_897_, 0, v_config_890_);
lean_ctor_set_uint64(v___x_897_, sizeof(void*)*1, v_key_896_);
lean_inc(v_canUnfold_x3f_885_);
lean_inc(v_synthPendingDepth_884_);
lean_inc(v_defEqCtx_x3f_883_);
lean_inc_ref(v_localInstances_882_);
lean_inc_ref(v_lctx_881_);
lean_inc(v_zetaDeltaSet_880_);
v___x_898_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v_zetaDeltaSet_880_);
lean_ctor_set(v___x_898_, 2, v_lctx_881_);
lean_ctor_set(v___x_898_, 3, v_localInstances_882_);
lean_ctor_set(v___x_898_, 4, v_defEqCtx_x3f_883_);
lean_ctor_set(v___x_898_, 5, v_synthPendingDepth_884_);
lean_ctor_set(v___x_898_, 6, v_canUnfold_x3f_885_);
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*7, v_trackZetaDelta_879_);
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*7 + 1, v_univApprox_886_);
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*7 + 2, v_inTypeClassResolution_887_);
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*7 + 3, v_cacheInferType_888_);
v___x_899_ = l_Lean_MVarId_apply(v_g_707_, v_e_708_, v_cfg_709_, v___x_710_, v___x_898_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_899_);
v___x_901_ = lean_box(0);
v___x_902_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__5(v___x_855_, v_hasTrace_721_, v_a_900_, v___x_901_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_List_reverse___redArg(v_a_903_);
v___y_801_ = v_a_853_;
v___y_802_ = v___x_856_;
v_a_803_ = v___x_904_;
goto v___jp_800_;
}
else
{
v___y_808_ = v_a_853_;
v___y_809_ = v___x_856_;
v___y_810_ = v___x_902_;
goto v___jp_807_;
}
}
else
{
v___y_808_ = v_a_853_;
v___y_809_ = v___x_856_;
v___y_810_ = v___x_899_;
goto v___jp_807_;
}
}
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v_foApprox_909_; uint8_t v_ctxApprox_910_; uint8_t v_quasiPatternApprox_911_; uint8_t v_constApprox_912_; uint8_t v_isDefEqStuckEx_913_; uint8_t v_unificationHints_914_; uint8_t v_proofIrrelevance_915_; uint8_t v_assignSyntheticOpaque_916_; uint8_t v_offsetCnstrs_917_; uint8_t v_etaStruct_918_; uint8_t v_univApprox_919_; uint8_t v_iota_920_; uint8_t v_beta_921_; uint8_t v_proj_922_; uint8_t v_zeta_923_; uint8_t v_zetaDelta_924_; uint8_t v_zetaUnused_925_; uint8_t v_zetaHave_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_957_; 
lean_del_object(v___x_782_);
v___x_907_ = lean_io_get_num_heartbeats();
v___x_908_ = l_Lean_Meta_Context_config(v___y_715_);
v_foApprox_909_ = lean_ctor_get_uint8(v___x_908_, 0);
v_ctxApprox_910_ = lean_ctor_get_uint8(v___x_908_, 1);
v_quasiPatternApprox_911_ = lean_ctor_get_uint8(v___x_908_, 2);
v_constApprox_912_ = lean_ctor_get_uint8(v___x_908_, 3);
v_isDefEqStuckEx_913_ = lean_ctor_get_uint8(v___x_908_, 4);
v_unificationHints_914_ = lean_ctor_get_uint8(v___x_908_, 5);
v_proofIrrelevance_915_ = lean_ctor_get_uint8(v___x_908_, 6);
v_assignSyntheticOpaque_916_ = lean_ctor_get_uint8(v___x_908_, 7);
v_offsetCnstrs_917_ = lean_ctor_get_uint8(v___x_908_, 8);
v_etaStruct_918_ = lean_ctor_get_uint8(v___x_908_, 10);
v_univApprox_919_ = lean_ctor_get_uint8(v___x_908_, 11);
v_iota_920_ = lean_ctor_get_uint8(v___x_908_, 12);
v_beta_921_ = lean_ctor_get_uint8(v___x_908_, 13);
v_proj_922_ = lean_ctor_get_uint8(v___x_908_, 14);
v_zeta_923_ = lean_ctor_get_uint8(v___x_908_, 15);
v_zetaDelta_924_ = lean_ctor_get_uint8(v___x_908_, 16);
v_zetaUnused_925_ = lean_ctor_get_uint8(v___x_908_, 17);
v_zetaHave_926_ = lean_ctor_get_uint8(v___x_908_, 18);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_957_ == 0)
{
v___x_928_ = v___x_908_;
v_isShared_929_ = v_isSharedCheck_957_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_908_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_957_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
uint8_t v_trackZetaDelta_930_; lean_object* v_zetaDeltaSet_931_; lean_object* v_lctx_932_; lean_object* v_localInstances_933_; lean_object* v_defEqCtx_x3f_934_; lean_object* v_synthPendingDepth_935_; lean_object* v_canUnfold_x3f_936_; uint8_t v_univApprox_937_; uint8_t v_inTypeClassResolution_938_; uint8_t v_cacheInferType_939_; lean_object* v_config_941_; 
v_trackZetaDelta_930_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7);
v_zetaDeltaSet_931_ = lean_ctor_get(v___y_715_, 1);
v_lctx_932_ = lean_ctor_get(v___y_715_, 2);
v_localInstances_933_ = lean_ctor_get(v___y_715_, 3);
v_defEqCtx_x3f_934_ = lean_ctor_get(v___y_715_, 4);
v_synthPendingDepth_935_ = lean_ctor_get(v___y_715_, 5);
v_canUnfold_x3f_936_ = lean_ctor_get(v___y_715_, 6);
v_univApprox_937_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_938_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 2);
v_cacheInferType_939_ = lean_ctor_get_uint8(v___y_715_, sizeof(void*)*7 + 3);
if (v_isShared_929_ == 0)
{
v_config_941_ = v___x_928_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 0, v_foApprox_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 1, v_ctxApprox_910_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 2, v_quasiPatternApprox_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 3, v_constApprox_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 4, v_isDefEqStuckEx_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 5, v_unificationHints_914_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 6, v_proofIrrelevance_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 7, v_assignSyntheticOpaque_916_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 8, v_offsetCnstrs_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 10, v_etaStruct_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 11, v_univApprox_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 12, v_iota_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 13, v_beta_921_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 14, v_proj_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 15, v_zeta_923_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 16, v_zetaDelta_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 17, v_zetaUnused_925_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, 18, v_zetaHave_926_);
v_config_941_ = v_reuseFailAlloc_956_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
uint64_t v___x_942_; uint64_t v___x_943_; uint64_t v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; uint64_t v_key_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_ctor_set_uint8(v_config_941_, 9, v_transparency_706_);
v___x_942_ = l_Lean_Meta_Context_configKey(v___y_715_);
v___x_943_ = 2ULL;
v___x_944_ = lean_uint64_shift_right(v___x_942_, v___x_943_);
v___x_945_ = lean_uint64_shift_left(v___x_944_, v___x_943_);
v___x_946_ = l_Lean_Meta_TransparencyMode_toUInt64(v_transparency_706_);
v_key_947_ = lean_uint64_lor(v___x_945_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_948_, 0, v_config_941_);
lean_ctor_set_uint64(v___x_948_, sizeof(void*)*1, v_key_947_);
lean_inc(v_canUnfold_x3f_936_);
lean_inc(v_synthPendingDepth_935_);
lean_inc(v_defEqCtx_x3f_934_);
lean_inc_ref(v_localInstances_933_);
lean_inc_ref(v_lctx_932_);
lean_inc(v_zetaDeltaSet_931_);
v___x_949_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_zetaDeltaSet_931_);
lean_ctor_set(v___x_949_, 2, v_lctx_932_);
lean_ctor_set(v___x_949_, 3, v_localInstances_933_);
lean_ctor_set(v___x_949_, 4, v_defEqCtx_x3f_934_);
lean_ctor_set(v___x_949_, 5, v_synthPendingDepth_935_);
lean_ctor_set(v___x_949_, 6, v_canUnfold_x3f_936_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*7, v_trackZetaDelta_930_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*7 + 1, v_univApprox_937_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*7 + 2, v_inTypeClassResolution_938_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*7 + 3, v_cacheInferType_939_);
v___x_950_ = l_Lean_MVarId_apply(v_g_707_, v_e_708_, v_cfg_709_, v___x_710_, v___x_949_, v___y_716_, v___y_717_, v___y_718_);
lean_dec_ref(v___x_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref(v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = l_List_filterAuxM___at___00Lean_Meta_SolveByElim_applyTactics_spec__6(v___x_855_, v_a_951_, v___x_952_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref(v___x_953_);
v___x_955_ = l_List_reverse___redArg(v_a_954_);
v___y_834_ = v___x_907_;
v___y_835_ = v_a_853_;
v_a_836_ = v___x_955_;
goto v___jp_833_;
}
else
{
v___y_839_ = v___x_907_;
v___y_840_ = v_a_853_;
v___y_841_ = v___x_953_;
goto v___jp_838_;
}
}
else
{
v___y_839_ = v___x_907_;
v___y_840_ = v_a_853_;
v___y_841_ = v___x_950_;
goto v___jp_838_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed(lean_object* v_transparency_1019_, lean_object* v_g_1020_, lean_object* v_e_1021_, lean_object* v_cfg_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v___f_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
uint8_t v_transparency_boxed_1033_; uint8_t v___x_14282__boxed_1034_; lean_object* v_res_1035_; 
v_transparency_boxed_1033_ = lean_unbox(v_transparency_1019_);
v___x_14282__boxed_1034_ = lean_unbox(v___x_1025_);
v_res_1035_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1(v_transparency_boxed_1033_, v_g_1020_, v_e_1021_, v_cfg_1022_, v___x_1023_, v___x_1024_, v___x_14282__boxed_1034_, v___x_1026_, v___f_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(uint8_t v_transparency_1037_, lean_object* v_g_1038_, lean_object* v_cfg_1039_, lean_object* v_e_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; 
lean_inc_ref(v_e_1040_);
v___f_1046_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1046_, 0, v_e_1040_);
v___x_1047_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_1048_ = lean_box(0);
v___x_1049_ = 1;
v___x_1050_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_1051_ = lean_box(v_transparency_1037_);
v___x_1052_ = lean_box(v___x_1049_);
v___f_1053_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_1053_, 0, v___x_1051_);
lean_closure_set(v___f_1053_, 1, v_g_1038_);
lean_closure_set(v___f_1053_, 2, v_e_1040_);
lean_closure_set(v___f_1053_, 3, v_cfg_1039_);
lean_closure_set(v___f_1053_, 4, v___x_1048_);
lean_closure_set(v___f_1053_, 5, v___x_1047_);
lean_closure_set(v___f_1053_, 6, v___x_1052_);
lean_closure_set(v___f_1053_, 7, v___x_1050_);
lean_closure_set(v___f_1053_, 8, v___f_1046_);
v___x_1054_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(v___f_1053_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed(lean_object* v_transparency_1055_, lean_object* v_g_1056_, lean_object* v_cfg_1057_, lean_object* v_e_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v_transparency_boxed_1064_; lean_object* v_res_1065_; 
v_transparency_boxed_1064_ = lean_unbox(v_transparency_1055_);
v_res_1065_ = l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2(v_transparency_boxed_1064_, v_g_1056_, v_cfg_1057_, v_e_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg(lean_object* v_cfg_1066_, uint8_t v_transparency_1067_, lean_object* v_lemmas_1068_, lean_object* v_g_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Iterator_ofList___redArg(v_lemmas_1068_, v_a_1070_, v_a_1071_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1084_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1084_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1084_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1078_ = lean_box(v_transparency_1067_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1079_, 0, v___x_1078_);
lean_closure_set(v___f_1079_, 1, v_g_1069_);
lean_closure_set(v___f_1079_, 2, v_cfg_1066_);
v___x_1080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed), 9, 4);
lean_closure_set(v___x_1080_, 0, lean_box(0));
lean_closure_set(v___x_1080_, 1, lean_box(0));
lean_closure_set(v___x_1080_, 2, v___f_1079_);
lean_closure_set(v___x_1080_, 3, v_a_1074_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1080_);
v___x_1082_ = v___x_1076_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_g_1069_);
lean_dec_ref(v_cfg_1066_);
v_a_1085_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1073_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1073_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___redArg___boxed(lean_object* v_cfg_1093_, lean_object* v_transparency_1094_, lean_object* v_lemmas_1095_, lean_object* v_g_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v_transparency_boxed_1100_; lean_object* v_res_1101_; 
v_transparency_boxed_1100_ = lean_unbox(v_transparency_1094_);
v_res_1101_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1093_, v_transparency_boxed_1100_, v_lemmas_1095_, v_g_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* v_cfg_1102_, uint8_t v_transparency_1103_, lean_object* v_lemmas_1104_, lean_object* v_g_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1102_, v_transparency_1103_, v_lemmas_1104_, v_g_1105_, v_a_1107_, v_a_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* v_cfg_1112_, lean_object* v_transparency_1113_, lean_object* v_lemmas_1114_, lean_object* v_g_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
uint8_t v_transparency_boxed_1121_; lean_object* v_res_1122_; 
v_transparency_boxed_1121_ = lean_unbox(v_transparency_1113_);
v_res_1122_ = l_Lean_Meta_SolveByElim_applyTactics(v_cfg_1112_, v_transparency_boxed_1121_, v_lemmas_1114_, v_g_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6(lean_object* v_00_u03b1_1123_, lean_object* v_x_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___redArg(v_x_1124_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__6(v_00_u03b1_1131_, v_x_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* v_cfg_1139_, uint8_t v_transparency_1140_, lean_object* v_lemmas_1141_, lean_object* v_g_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_cfg_1139_, v_transparency_1140_, v_lemmas_1141_, v_g_1142_, v_a_1144_, v_a_1146_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l_Lean_Meta_Iterator_head___redArg(v_a_1149_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
return v___x_1150_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_a_1151_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1148_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1148_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* v_cfg_1159_, lean_object* v_transparency_1160_, lean_object* v_lemmas_1161_, lean_object* v_g_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v_transparency_boxed_1168_; lean_object* v_res_1169_; 
v_transparency_boxed_1168_ = lean_unbox(v_transparency_1160_);
v_res_1169_ = l_Lean_Meta_SolveByElim_applyFirst(v_cfg_1159_, v_transparency_boxed_1168_, v_lemmas_1161_, v_g_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(lean_object* v_x_1170_){
_start:
{
lean_object* v_toApplyRulesConfig_1171_; lean_object* v_toBacktrackConfig_1172_; 
v_toApplyRulesConfig_1171_ = lean_ctor_get(v_x_1170_, 0);
v_toBacktrackConfig_1172_ = lean_ctor_get(v_toApplyRulesConfig_1171_, 0);
lean_inc_ref(v_toBacktrackConfig_1172_);
return v_toBacktrackConfig_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0___boxed(lean_object* v_x_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___lam__0(v_x_1173_);
lean_dec_ref(v_x_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(lean_object* v_test_1177_, lean_object* v_discharge_1178_, lean_object* v_g_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v_g_1179_);
v___x_1185_ = lean_apply_6(v_test_1177_, v_g_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, lean_box(0));
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1196_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_unbox(v_a_1186_);
lean_dec(v_a_1186_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
lean_del_object(v___x_1188_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
v___x_1191_ = lean_apply_6(v_discharge_1178_, v_g_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, lean_box(0));
return v___x_1191_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_dec(v_g_1179_);
lean_dec_ref(v_discharge_1178_);
v___x_1192_ = lean_box(0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1192_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_g_1179_);
lean_dec_ref(v_discharge_1178_);
v_a_1197_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1185_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1185_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed(lean_object* v_test_1205_, lean_object* v_discharge_1206_, lean_object* v_g_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0(v_test_1205_, v_discharge_1206_, v_g_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* v_cfg_1214_, lean_object* v_test_1215_){
_start:
{
lean_object* v_toApplyRulesConfig_1216_; lean_object* v_toBacktrackConfig_1217_; uint8_t v_backtracking_1218_; uint8_t v_intro_1219_; uint8_t v_constructor_1220_; uint8_t v_suggestions_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1253_; 
v_toApplyRulesConfig_1216_ = lean_ctor_get(v_cfg_1214_, 0);
lean_inc_ref(v_toApplyRulesConfig_1216_);
v_toBacktrackConfig_1217_ = lean_ctor_get(v_toApplyRulesConfig_1216_, 0);
lean_inc_ref(v_toBacktrackConfig_1217_);
v_backtracking_1218_ = lean_ctor_get_uint8(v_cfg_1214_, sizeof(void*)*1);
v_intro_1219_ = lean_ctor_get_uint8(v_cfg_1214_, sizeof(void*)*1 + 1);
v_constructor_1220_ = lean_ctor_get_uint8(v_cfg_1214_, sizeof(void*)*1 + 2);
v_suggestions_1221_ = lean_ctor_get_uint8(v_cfg_1214_, sizeof(void*)*1 + 3);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_cfg_1214_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_cfg_1214_, 0);
lean_dec(v_unused_1254_);
v___x_1223_ = v_cfg_1214_;
v_isShared_1224_ = v_isSharedCheck_1253_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v_cfg_1214_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1253_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_toApplyConfig_1225_; uint8_t v_transparency_1226_; uint8_t v_symm_1227_; uint8_t v_exfalso_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1251_; 
v_toApplyConfig_1225_ = lean_ctor_get(v_toApplyRulesConfig_1216_, 1);
v_transparency_1226_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1216_, sizeof(void*)*2);
v_symm_1227_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1216_, sizeof(void*)*2 + 1);
v_exfalso_1228_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1216_, sizeof(void*)*2 + 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_toApplyRulesConfig_1216_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_toApplyRulesConfig_1216_, 0);
lean_dec(v_unused_1252_);
v___x_1230_ = v_toApplyRulesConfig_1216_;
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_toApplyConfig_1225_);
lean_dec(v_toApplyRulesConfig_1216_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_maxDepth_1232_; lean_object* v_proc_1233_; lean_object* v_suspend_1234_; lean_object* v_discharge_1235_; uint8_t v_commitIndependentGoals_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1250_; 
v_maxDepth_1232_ = lean_ctor_get(v_toBacktrackConfig_1217_, 0);
v_proc_1233_ = lean_ctor_get(v_toBacktrackConfig_1217_, 1);
v_suspend_1234_ = lean_ctor_get(v_toBacktrackConfig_1217_, 2);
v_discharge_1235_ = lean_ctor_get(v_toBacktrackConfig_1217_, 3);
v_commitIndependentGoals_1236_ = lean_ctor_get_uint8(v_toBacktrackConfig_1217_, sizeof(void*)*4);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_toBacktrackConfig_1217_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1238_ = v_toBacktrackConfig_1217_;
v_isShared_1239_ = v_isSharedCheck_1250_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_discharge_1235_);
lean_inc(v_suspend_1234_);
lean_inc(v_proc_1233_);
lean_inc(v_maxDepth_1232_);
lean_dec(v_toBacktrackConfig_1217_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1250_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___f_1240_; lean_object* v___x_1242_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1240_, 0, v_test_1215_);
lean_closure_set(v___f_1240_, 1, v_discharge_1235_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 3, v___f_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_maxDepth_1232_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_proc_1233_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_suspend_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v___f_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*4, v_commitIndependentGoals_1236_);
v___x_1242_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1242_);
v___x_1244_ = v___x_1230_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_toApplyConfig_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1248_, sizeof(void*)*2, v_transparency_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1248_, sizeof(void*)*2 + 1, v_symm_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1248_, sizeof(void*)*2 + 2, v_exfalso_1228_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1244_);
v___x_1246_ = v___x_1223_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1247_, sizeof(void*)*1, v_backtracking_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1247_, sizeof(void*)*1 + 1, v_intro_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1247_, sizeof(void*)*1 + 2, v_constructor_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1247_, sizeof(void*)*1 + 3, v_suggestions_1221_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(lean_object* v_proc_1255_, lean_object* v_proc_1256_, lean_object* v_orig_1257_, lean_object* v_goals_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
if (lean_obj_tag(v_goals_1258_) == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v_proc_1256_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
v___x_1264_ = lean_apply_7(v_proc_1255_, v_orig_1257_, v_goals_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, lean_box(0));
return v___x_1264_;
}
else
{
lean_object* v_head_1265_; lean_object* v_tail_1266_; lean_object* v___x_1267_; 
v_head_1265_ = lean_ctor_get(v_goals_1258_, 0);
v_tail_1266_ = lean_ctor_get(v_goals_1258_, 1);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v_head_1265_);
v___x_1267_ = lean_apply_6(v_proc_1256_, v_head_1265_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, lean_box(0));
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1277_; 
lean_inc(v_tail_1266_);
lean_dec_ref(v_goals_1258_);
lean_dec(v_orig_1257_);
lean_dec_ref(v_proc_1255_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = l_List_appendTR___redArg(v_a_1268_, v_tail_1266_);
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1290_; 
v_a_1278_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1280_ = v___x_1267_;
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1267_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
uint8_t v___y_1283_; uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_Exception_isInterrupt(v_a_1278_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
lean_inc(v_a_1278_);
v___x_1289_ = l_Lean_Exception_isRuntime(v_a_1278_);
v___y_1283_ = v___x_1289_;
goto v___jp_1282_;
}
else
{
v___y_1283_ = v___x_1288_;
goto v___jp_1282_;
}
v___jp_1282_:
{
if (v___y_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_del_object(v___x_1280_);
lean_dec(v_a_1278_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
v___x_1284_ = lean_apply_7(v_proc_1255_, v_orig_1257_, v_goals_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, lean_box(0));
return v___x_1284_;
}
else
{
lean_object* v___x_1286_; 
lean_dec_ref(v_goals_1258_);
lean_dec(v_orig_1257_);
lean_dec_ref(v_proc_1255_);
if (v_isShared_1281_ == 0)
{
v___x_1286_ = v___x_1280_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1278_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed(lean_object* v_proc_1291_, lean_object* v_proc_1292_, lean_object* v_orig_1293_, lean_object* v_goals_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0(v_proc_1291_, v_proc_1292_, v_orig_1293_, v_goals_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* v_cfg_1301_, lean_object* v_proc_1302_){
_start:
{
lean_object* v_toApplyRulesConfig_1303_; lean_object* v_toBacktrackConfig_1304_; uint8_t v_backtracking_1305_; uint8_t v_intro_1306_; uint8_t v_constructor_1307_; uint8_t v_suggestions_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1340_; 
v_toApplyRulesConfig_1303_ = lean_ctor_get(v_cfg_1301_, 0);
lean_inc_ref(v_toApplyRulesConfig_1303_);
v_toBacktrackConfig_1304_ = lean_ctor_get(v_toApplyRulesConfig_1303_, 0);
lean_inc_ref(v_toBacktrackConfig_1304_);
v_backtracking_1305_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*1);
v_intro_1306_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*1 + 1);
v_constructor_1307_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*1 + 2);
v_suggestions_1308_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*1 + 3);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_cfg_1301_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_cfg_1301_, 0);
lean_dec(v_unused_1341_);
v___x_1310_ = v_cfg_1301_;
v_isShared_1311_ = v_isSharedCheck_1340_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v_cfg_1301_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1340_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_toApplyConfig_1312_; uint8_t v_transparency_1313_; uint8_t v_symm_1314_; uint8_t v_exfalso_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1338_; 
v_toApplyConfig_1312_ = lean_ctor_get(v_toApplyRulesConfig_1303_, 1);
v_transparency_1313_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1303_, sizeof(void*)*2);
v_symm_1314_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1303_, sizeof(void*)*2 + 1);
v_exfalso_1315_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1303_, sizeof(void*)*2 + 2);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_toApplyRulesConfig_1303_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_toApplyRulesConfig_1303_, 0);
lean_dec(v_unused_1339_);
v___x_1317_ = v_toApplyRulesConfig_1303_;
v_isShared_1318_ = v_isSharedCheck_1338_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_toApplyConfig_1312_);
lean_dec(v_toApplyRulesConfig_1303_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1338_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_maxDepth_1319_; lean_object* v_proc_1320_; lean_object* v_suspend_1321_; lean_object* v_discharge_1322_; uint8_t v_commitIndependentGoals_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1337_; 
v_maxDepth_1319_ = lean_ctor_get(v_toBacktrackConfig_1304_, 0);
v_proc_1320_ = lean_ctor_get(v_toBacktrackConfig_1304_, 1);
v_suspend_1321_ = lean_ctor_get(v_toBacktrackConfig_1304_, 2);
v_discharge_1322_ = lean_ctor_get(v_toBacktrackConfig_1304_, 3);
v_commitIndependentGoals_1323_ = lean_ctor_get_uint8(v_toBacktrackConfig_1304_, sizeof(void*)*4);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_toBacktrackConfig_1304_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1325_ = v_toBacktrackConfig_1304_;
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_discharge_1322_);
lean_inc(v_suspend_1321_);
lean_inc(v_proc_1320_);
lean_inc(v_maxDepth_1319_);
lean_dec(v_toBacktrackConfig_1304_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___f_1327_; lean_object* v___x_1329_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1327_, 0, v_proc_1320_);
lean_closure_set(v___f_1327_, 1, v_proc_1302_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v___f_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_maxDepth_1319_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___f_1327_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_suspend_1321_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_discharge_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1336_, sizeof(void*)*4, v_commitIndependentGoals_1323_);
v___x_1329_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1329_);
v___x_1331_ = v___x_1317_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_toApplyConfig_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*2, v_transparency_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*2 + 1, v_symm_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*2 + 2, v_exfalso_1315_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1331_);
v___x_1333_ = v___x_1310_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*1, v_backtracking_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*1 + 1, v_intro_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*1 + 2, v_constructor_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*1 + 3, v_suggestions_1308_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(lean_object* v_g_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = 1;
v___x_1349_ = l_Lean_Meta_intro1Core(v_g_1342_, v___x_1348_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1367_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1367_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1367_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_snd_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1365_; 
v_snd_1354_ = lean_ctor_get(v_a_1350_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_a_1350_, 0);
lean_dec(v_unused_1366_);
v___x_1356_ = v_a_1350_;
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_snd_1354_);
lean_dec(v_a_1350_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_box(0);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 1);
lean_ctor_set(v___x_1356_, 1, v___x_1358_);
lean_ctor_set(v___x_1356_, 0, v_snd_1354_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_snd_1354_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1360_);
v___x_1362_ = v___x_1352_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
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
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1349_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1349_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0___boxed(lean_object* v_g_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lam__0(v_g_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* v_cfg_1384_){
_start:
{
lean_object* v___f_1385_; lean_object* v___x_1386_; 
v___f_1385_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__0));
v___x_1386_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1384_, v___f_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v_ks_1391_; lean_object* v_vs_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1416_; 
v_ks_1391_ = lean_ctor_get(v_x_1387_, 0);
v_vs_1392_ = lean_ctor_get(v_x_1387_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_x_1387_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1394_ = v_x_1387_;
v_isShared_1395_ = v_isSharedCheck_1416_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_vs_1392_);
lean_inc(v_ks_1391_);
lean_dec(v_x_1387_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1416_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = lean_array_get_size(v_ks_1391_);
v___x_1397_ = lean_nat_dec_lt(v_x_1388_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec(v_x_1388_);
v___x_1398_ = lean_array_push(v_ks_1391_, v_x_1389_);
v___x_1399_ = lean_array_push(v_vs_1392_, v_x_1390_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v___x_1399_);
lean_ctor_set(v___x_1394_, 0, v___x_1398_);
v___x_1401_ = v___x_1394_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
lean_object* v_k_x27_1403_; uint8_t v___x_1404_; 
v_k_x27_1403_ = lean_array_fget_borrowed(v_ks_1391_, v_x_1388_);
v___x_1404_ = l_Lean_instBEqMVarId_beq(v_x_1389_, v_k_x27_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; 
if (v_isShared_1395_ == 0)
{
v___x_1406_ = v___x_1394_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_ks_1391_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_vs_1392_);
v___x_1406_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_add(v_x_1388_, v___x_1407_);
lean_dec(v_x_1388_);
v_x_1387_ = v___x_1406_;
v_x_1388_ = v___x_1408_;
goto _start;
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1411_ = lean_array_fset(v_ks_1391_, v_x_1388_, v_x_1389_);
v___x_1412_ = lean_array_fset(v_vs_1392_, v_x_1388_, v_x_1390_);
lean_dec(v_x_1388_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v___x_1412_);
lean_ctor_set(v___x_1394_, 0, v___x_1411_);
v___x_1414_ = v___x_1394_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1412_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1417_, lean_object* v_k_1418_, lean_object* v_v_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1417_, v___x_1420_, v_k_1418_, v_v_1419_);
return v___x_1421_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; 
v___x_1422_ = ((size_t)5ULL);
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_shift_left(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; 
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1427_ = lean_usize_sub(v___x_1426_, v___x_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1429_, size_t v_x_1430_, size_t v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v_es_1434_; size_t v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; size_t v___x_1438_; lean_object* v_j_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_es_1434_ = lean_ctor_get(v_x_1429_, 0);
v___x_1435_ = ((size_t)5ULL);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1438_ = lean_usize_land(v_x_1430_, v___x_1437_);
v_j_1439_ = lean_usize_to_nat(v___x_1438_);
v___x_1440_ = lean_array_get_size(v_es_1434_);
v___x_1441_ = lean_nat_dec_lt(v_j_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec(v_j_1439_);
lean_dec(v_x_1433_);
lean_dec(v_x_1432_);
return v_x_1429_;
}
else
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1478_; 
lean_inc_ref(v_es_1434_);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_x_1429_, 0);
lean_dec(v_unused_1479_);
v___x_1443_ = v_x_1429_;
v_isShared_1444_ = v_isSharedCheck_1478_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_x_1429_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1478_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_v_1445_; lean_object* v___x_1446_; lean_object* v_xs_x27_1447_; lean_object* v___y_1449_; 
v_v_1445_ = lean_array_fget(v_es_1434_, v_j_1439_);
v___x_1446_ = lean_box(0);
v_xs_x27_1447_ = lean_array_fset(v_es_1434_, v_j_1439_, v___x_1446_);
switch(lean_obj_tag(v_v_1445_))
{
case 0:
{
lean_object* v_key_1454_; lean_object* v_val_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1465_; 
v_key_1454_ = lean_ctor_get(v_v_1445_, 0);
v_val_1455_ = lean_ctor_get(v_v_1445_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_v_1445_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1457_ = v_v_1445_;
v_isShared_1458_ = v_isSharedCheck_1465_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_val_1455_);
lean_inc(v_key_1454_);
lean_dec(v_v_1445_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1465_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___x_1459_; 
v___x_1459_ = l_Lean_instBEqMVarId_beq(v_x_1432_, v_key_1454_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_del_object(v___x_1457_);
v___x_1460_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1454_, v_val_1455_, v_x_1432_, v_x_1433_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___y_1449_ = v___x_1461_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_val_1455_);
lean_dec(v_key_1454_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v_x_1433_);
lean_ctor_set(v___x_1457_, 0, v_x_1432_);
v___x_1463_ = v___x_1457_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_x_1432_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_x_1433_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
v___y_1449_ = v___x_1463_;
goto v___jp_1448_;
}
}
}
}
case 1:
{
lean_object* v_node_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1476_; 
v_node_1466_ = lean_ctor_get(v_v_1445_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_v_1445_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1468_ = v_v_1445_;
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_node_1466_);
lean_dec(v_v_1445_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1476_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1470_ = lean_usize_shift_right(v_x_1430_, v___x_1435_);
v___x_1471_ = lean_usize_add(v_x_1431_, v___x_1436_);
v___x_1472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_node_1466_, v___x_1470_, v___x_1471_, v_x_1432_, v_x_1433_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1472_);
v___x_1474_ = v___x_1468_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
v___y_1449_ = v___x_1474_;
goto v___jp_1448_;
}
}
}
default: 
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_x_1432_);
lean_ctor_set(v___x_1477_, 1, v_x_1433_);
v___y_1449_ = v___x_1477_;
goto v___jp_1448_;
}
}
v___jp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_array_fset(v_xs_x27_1447_, v_j_1439_, v___y_1449_);
lean_dec(v_j_1439_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1450_);
v___x_1452_ = v___x_1443_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
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
else
{
lean_object* v_ks_1480_; lean_object* v_vs_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1501_; 
v_ks_1480_ = lean_ctor_get(v_x_1429_, 0);
v_vs_1481_ = lean_ctor_get(v_x_1429_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1429_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1483_ = v_x_1429_;
v_isShared_1484_ = v_isSharedCheck_1501_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_vs_1481_);
lean_inc(v_ks_1480_);
lean_dec(v_x_1429_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1501_;
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
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_ks_1480_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_vs_1481_);
v___x_1486_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v_newNode_1487_; uint8_t v___y_1489_; size_t v___x_1495_; uint8_t v___x_1496_; 
v_newNode_1487_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1486_, v_x_1432_, v_x_1433_);
v___x_1495_ = ((size_t)7ULL);
v___x_1496_ = lean_usize_dec_le(v___x_1495_, v_x_1431_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1487_);
v___x_1498_ = lean_unsigned_to_nat(4u);
v___x_1499_ = lean_nat_dec_lt(v___x_1497_, v___x_1498_);
lean_dec(v___x_1497_);
v___y_1489_ = v___x_1499_;
goto v___jp_1488_;
}
else
{
v___y_1489_ = v___x_1496_;
goto v___jp_1488_;
}
v___jp_1488_:
{
if (v___y_1489_ == 0)
{
lean_object* v_ks_1490_; lean_object* v_vs_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_ks_1490_ = lean_ctor_get(v_newNode_1487_, 0);
lean_inc_ref(v_ks_1490_);
v_vs_1491_ = lean_ctor_get(v_newNode_1487_, 1);
lean_inc_ref(v_vs_1491_);
lean_dec_ref(v_newNode_1487_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1431_, v_ks_1490_, v_vs_1491_, v___x_1492_, v___x_1493_);
lean_dec_ref(v_vs_1491_);
lean_dec_ref(v_ks_1490_);
return v___x_1494_;
}
else
{
return v_newNode_1487_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1502_, lean_object* v_keys_1503_, lean_object* v_vals_1504_, lean_object* v_i_1505_, lean_object* v_entries_1506_){
_start:
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = lean_array_get_size(v_keys_1503_);
v___x_1508_ = lean_nat_dec_lt(v_i_1505_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec(v_i_1505_);
return v_entries_1506_;
}
else
{
lean_object* v_k_1509_; lean_object* v_v_1510_; uint64_t v___x_1511_; size_t v_h_1512_; size_t v___x_1513_; lean_object* v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; size_t v_h_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_k_1509_ = lean_array_fget_borrowed(v_keys_1503_, v_i_1505_);
v_v_1510_ = lean_array_fget_borrowed(v_vals_1504_, v_i_1505_);
v___x_1511_ = l_Lean_instHashableMVarId_hash(v_k_1509_);
v_h_1512_ = lean_uint64_to_usize(v___x_1511_);
v___x_1513_ = ((size_t)5ULL);
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_sub(v_depth_1502_, v___x_1515_);
v___x_1517_ = lean_usize_mul(v___x_1513_, v___x_1516_);
v_h_1518_ = lean_usize_shift_right(v_h_1512_, v___x_1517_);
v___x_1519_ = lean_nat_add(v_i_1505_, v___x_1514_);
lean_dec(v_i_1505_);
lean_inc(v_v_1510_);
lean_inc(v_k_1509_);
v___x_1520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_entries_1506_, v_h_1518_, v_depth_1502_, v_k_1509_, v_v_1510_);
v_i_1505_ = v___x_1519_;
v_entries_1506_ = v___x_1520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1522_, lean_object* v_keys_1523_, lean_object* v_vals_1524_, lean_object* v_i_1525_, lean_object* v_entries_1526_){
_start:
{
size_t v_depth_boxed_1527_; lean_object* v_res_1528_; 
v_depth_boxed_1527_ = lean_unbox_usize(v_depth_1522_);
lean_dec(v_depth_1522_);
v_res_1528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1527_, v_keys_1523_, v_vals_1524_, v_i_1525_, v_entries_1526_);
lean_dec_ref(v_vals_1524_);
lean_dec_ref(v_keys_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
size_t v_x_834__boxed_1534_; size_t v_x_835__boxed_1535_; lean_object* v_res_1536_; 
v_x_834__boxed_1534_ = lean_unbox_usize(v_x_1530_);
lean_dec(v_x_1530_);
v_x_835__boxed_1535_ = lean_unbox_usize(v_x_1531_);
lean_dec(v_x_1531_);
v_res_1536_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1529_, v_x_834__boxed_1534_, v_x_835__boxed_1535_, v_x_1532_, v_x_1533_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
uint64_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1540_ = l_Lean_instHashableMVarId_hash(v_x_1538_);
v___x_1541_ = lean_uint64_to_usize(v___x_1540_);
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1537_, v___x_1541_, v___x_1542_, v_x_1538_, v_x_1539_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(lean_object* v_mvarId_1544_, lean_object* v_val_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v_mctx_1549_; lean_object* v_cache_1550_; lean_object* v_zetaDeltaFVarIds_1551_; lean_object* v_postponed_1552_; lean_object* v_diag_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1580_; 
v___x_1548_ = lean_st_ref_take(v___y_1546_);
v_mctx_1549_ = lean_ctor_get(v___x_1548_, 0);
v_cache_1550_ = lean_ctor_get(v___x_1548_, 1);
v_zetaDeltaFVarIds_1551_ = lean_ctor_get(v___x_1548_, 2);
v_postponed_1552_ = lean_ctor_get(v___x_1548_, 3);
v_diag_1553_ = lean_ctor_get(v___x_1548_, 4);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1555_ = v___x_1548_;
v_isShared_1556_ = v_isSharedCheck_1580_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_diag_1553_);
lean_inc(v_postponed_1552_);
lean_inc(v_zetaDeltaFVarIds_1551_);
lean_inc(v_cache_1550_);
lean_inc(v_mctx_1549_);
lean_dec(v___x_1548_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1580_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_depth_1557_; lean_object* v_levelAssignDepth_1558_; lean_object* v_mvarCounter_1559_; lean_object* v_lDepth_1560_; lean_object* v_decls_1561_; lean_object* v_userNames_1562_; lean_object* v_lAssignment_1563_; lean_object* v_eAssignment_1564_; lean_object* v_dAssignment_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1579_; 
v_depth_1557_ = lean_ctor_get(v_mctx_1549_, 0);
v_levelAssignDepth_1558_ = lean_ctor_get(v_mctx_1549_, 1);
v_mvarCounter_1559_ = lean_ctor_get(v_mctx_1549_, 2);
v_lDepth_1560_ = lean_ctor_get(v_mctx_1549_, 3);
v_decls_1561_ = lean_ctor_get(v_mctx_1549_, 4);
v_userNames_1562_ = lean_ctor_get(v_mctx_1549_, 5);
v_lAssignment_1563_ = lean_ctor_get(v_mctx_1549_, 6);
v_eAssignment_1564_ = lean_ctor_get(v_mctx_1549_, 7);
v_dAssignment_1565_ = lean_ctor_get(v_mctx_1549_, 8);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_mctx_1549_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1567_ = v_mctx_1549_;
v_isShared_1568_ = v_isSharedCheck_1579_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_dAssignment_1565_);
lean_inc(v_eAssignment_1564_);
lean_inc(v_lAssignment_1563_);
lean_inc(v_userNames_1562_);
lean_inc(v_decls_1561_);
lean_inc(v_lDepth_1560_);
lean_inc(v_mvarCounter_1559_);
lean_inc(v_levelAssignDepth_1558_);
lean_inc(v_depth_1557_);
lean_dec(v_mctx_1549_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1579_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1569_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_eAssignment_1564_, v_mvarId_1544_, v_val_1545_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 7, v___x_1569_);
v___x_1571_ = v___x_1567_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_depth_1557_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_levelAssignDepth_1558_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_mvarCounter_1559_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_lDepth_1560_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_decls_1561_);
lean_ctor_set(v_reuseFailAlloc_1578_, 5, v_userNames_1562_);
lean_ctor_set(v_reuseFailAlloc_1578_, 6, v_lAssignment_1563_);
lean_ctor_set(v_reuseFailAlloc_1578_, 7, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1578_, 8, v_dAssignment_1565_);
v___x_1571_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1573_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1571_);
v___x_1573_ = v___x_1555_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_cache_1550_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_zetaDeltaFVarIds_1551_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_postponed_1552_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_diag_1553_);
v___x_1573_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_st_ref_set(v___y_1546_, v___x_1573_);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg___boxed(lean_object* v_mvarId_1581_, lean_object* v_val_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1581_, v_val_1582_, v___y_1583_);
lean_dec(v___y_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(lean_object* v_g_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
lean_inc(v_g_1586_);
v___x_1592_ = l_Lean_MVarId_getType(v_g_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lean_Meta_synthInstance(v_a_1593_, v___x_1594_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1605_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1586_, v_a_1596_, v___y_1588_);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1597_, 0);
lean_dec(v_unused_1606_);
v___x_1599_ = v___x_1597_;
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
else
{
lean_dec(v___x_1597_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1605_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_box(0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1601_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_g_1586_);
v_a_1607_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1595_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1595_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_g_1586_);
v_a_1615_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1592_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1592_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0___boxed(lean_object* v_g_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lam__0(v_g_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* v_cfg_1631_){
_start:
{
lean_object* v___f_1632_; lean_object* v___x_1633_; 
v___f_1632_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__0));
v___x_1633_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(v_cfg_1631_, v___f_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(lean_object* v_mvarId_1634_, lean_object* v_val_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_mvarId_1634_, v_val_1635_, v___y_1637_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___boxed(lean_object* v_mvarId_1642_, lean_object* v_val_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0(v_mvarId_1642_, v_val_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0(lean_object* v_00_u03b2_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0___redArg(v_x_1651_, v_x_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, size_t v_x_1657_, size_t v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg(v_x_1656_, v_x_1657_, v_x_1658_, v_x_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
size_t v_x_1165__boxed_1668_; size_t v_x_1166__boxed_1669_; lean_object* v_res_1670_; 
v_x_1165__boxed_1668_ = lean_unbox_usize(v_x_1664_);
lean_dec(v_x_1664_);
v_x_1166__boxed_1669_ = lean_unbox_usize(v_x_1665_);
lean_dec(v_x_1665_);
v_res_1670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1(v_00_u03b2_1662_, v_x_1663_, v_x_1165__boxed_1668_, v_x_1166__boxed_1669_, v_x_1666_, v_x_1667_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1671_, lean_object* v_n_1672_, lean_object* v_k_1673_, lean_object* v_v_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1672_, v_k_1673_, v_v_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1676_, size_t v_depth_1677_, lean_object* v_keys_1678_, lean_object* v_vals_1679_, lean_object* v_heq_1680_, lean_object* v_i_1681_, lean_object* v_entries_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1677_, v_keys_1678_, v_vals_1679_, v_i_1681_, v_entries_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1684_, lean_object* v_depth_1685_, lean_object* v_keys_1686_, lean_object* v_vals_1687_, lean_object* v_heq_1688_, lean_object* v_i_1689_, lean_object* v_entries_1690_){
_start:
{
size_t v_depth_boxed_1691_; lean_object* v_res_1692_; 
v_depth_boxed_1691_ = lean_unbox_usize(v_depth_1685_);
lean_dec(v_depth_1685_);
v_res_1692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1684_, v_depth_boxed_1691_, v_keys_1686_, v_vals_1687_, v_heq_1688_, v_i_1689_, v_entries_1690_);
lean_dec_ref(v_vals_1687_);
lean_dec_ref(v_keys_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_, lean_object* v_x_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1694_, v_x_1695_, v_x_1696_, v_x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(lean_object* v_discharge_1699_, lean_object* v_discharge_1700_, lean_object* v_g_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v_g_1701_);
v___x_1707_ = lean_apply_6(v_discharge_1699_, v_g_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec(v_g_1701_);
lean_dec_ref(v_discharge_1700_);
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; uint8_t v___y_1710_; uint8_t v___x_1712_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
v___x_1712_ = l_Lean_Exception_isInterrupt(v_a_1708_);
if (v___x_1712_ == 0)
{
uint8_t v___x_1713_; 
v___x_1713_ = l_Lean_Exception_isRuntime(v_a_1708_);
v___y_1710_ = v___x_1713_;
goto v___jp_1709_;
}
else
{
lean_dec(v_a_1708_);
v___y_1710_ = v___x_1712_;
goto v___jp_1709_;
}
v___jp_1709_:
{
if (v___y_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v___x_1707_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1711_ = lean_apply_6(v_discharge_1700_, v_g_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
return v___x_1711_;
}
else
{
lean_dec(v_g_1701_);
lean_dec_ref(v_discharge_1700_);
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed(lean_object* v_discharge_1714_, lean_object* v_discharge_1715_, lean_object* v_g_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0(v_discharge_1714_, v_discharge_1715_, v_g_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* v_cfg_1723_, lean_object* v_discharge_1724_){
_start:
{
lean_object* v_toApplyRulesConfig_1725_; lean_object* v_toBacktrackConfig_1726_; uint8_t v_backtracking_1727_; uint8_t v_intro_1728_; uint8_t v_constructor_1729_; uint8_t v_suggestions_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1762_; 
v_toApplyRulesConfig_1725_ = lean_ctor_get(v_cfg_1723_, 0);
lean_inc_ref(v_toApplyRulesConfig_1725_);
v_toBacktrackConfig_1726_ = lean_ctor_get(v_toApplyRulesConfig_1725_, 0);
lean_inc_ref(v_toBacktrackConfig_1726_);
v_backtracking_1727_ = lean_ctor_get_uint8(v_cfg_1723_, sizeof(void*)*1);
v_intro_1728_ = lean_ctor_get_uint8(v_cfg_1723_, sizeof(void*)*1 + 1);
v_constructor_1729_ = lean_ctor_get_uint8(v_cfg_1723_, sizeof(void*)*1 + 2);
v_suggestions_1730_ = lean_ctor_get_uint8(v_cfg_1723_, sizeof(void*)*1 + 3);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_cfg_1723_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v_cfg_1723_, 0);
lean_dec(v_unused_1763_);
v___x_1732_ = v_cfg_1723_;
v_isShared_1733_ = v_isSharedCheck_1762_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v_cfg_1723_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1762_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_toApplyConfig_1734_; uint8_t v_transparency_1735_; uint8_t v_symm_1736_; uint8_t v_exfalso_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1760_; 
v_toApplyConfig_1734_ = lean_ctor_get(v_toApplyRulesConfig_1725_, 1);
v_transparency_1735_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1725_, sizeof(void*)*2);
v_symm_1736_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1725_, sizeof(void*)*2 + 1);
v_exfalso_1737_ = lean_ctor_get_uint8(v_toApplyRulesConfig_1725_, sizeof(void*)*2 + 2);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_toApplyRulesConfig_1725_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_toApplyRulesConfig_1725_, 0);
lean_dec(v_unused_1761_);
v___x_1739_ = v_toApplyRulesConfig_1725_;
v_isShared_1740_ = v_isSharedCheck_1760_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_toApplyConfig_1734_);
lean_dec(v_toApplyRulesConfig_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1760_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_maxDepth_1741_; lean_object* v_proc_1742_; lean_object* v_suspend_1743_; lean_object* v_discharge_1744_; uint8_t v_commitIndependentGoals_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1759_; 
v_maxDepth_1741_ = lean_ctor_get(v_toBacktrackConfig_1726_, 0);
v_proc_1742_ = lean_ctor_get(v_toBacktrackConfig_1726_, 1);
v_suspend_1743_ = lean_ctor_get(v_toBacktrackConfig_1726_, 2);
v_discharge_1744_ = lean_ctor_get(v_toBacktrackConfig_1726_, 3);
v_commitIndependentGoals_1745_ = lean_ctor_get_uint8(v_toBacktrackConfig_1726_, sizeof(void*)*4);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_toBacktrackConfig_1726_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1747_ = v_toBacktrackConfig_1726_;
v_isShared_1748_ = v_isSharedCheck_1759_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_discharge_1744_);
lean_inc(v_suspend_1743_);
lean_inc(v_proc_1742_);
lean_inc(v_maxDepth_1741_);
lean_dec(v_toBacktrackConfig_1726_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1759_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___f_1749_; lean_object* v___x_1751_; 
v___f_1749_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1749_, 0, v_discharge_1724_);
lean_closure_set(v___f_1749_, 1, v_discharge_1744_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 3, v___f_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_maxDepth_1741_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_proc_1742_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_suspend_1743_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v___f_1749_);
lean_ctor_set_uint8(v_reuseFailAlloc_1758_, sizeof(void*)*4, v_commitIndependentGoals_1745_);
v___x_1751_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1751_);
v___x_1753_ = v___x_1739_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_toApplyConfig_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*2, v_transparency_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*2 + 1, v_symm_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*2 + 2, v_exfalso_1737_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1753_);
v___x_1755_ = v___x_1732_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*1, v_backtracking_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*1 + 1, v_intro_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*1 + 2, v_constructor_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*1 + 3, v_suggestions_1730_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(lean_object* v_g_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = 1;
v___x_1771_ = l_Lean_Meta_intro1Core(v_g_1764_, v___x_1770_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1790_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1790_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1790_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_snd_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1788_; 
v_snd_1776_ = lean_ctor_get(v_a_1772_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v_a_1772_, 0);
lean_dec(v_unused_1789_);
v___x_1778_ = v_a_1772_;
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snd_1776_);
lean_dec(v_a_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_box(0);
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 1);
lean_ctor_set(v___x_1778_, 1, v___x_1780_);
lean_ctor_set(v___x_1778_, 0, v_snd_1776_);
v___x_1782_ = v___x_1778_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_snd_1776_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1783_);
v___x_1785_ = v___x_1774_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1771_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1771_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0___boxed(lean_object* v_g_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lam__0(v_g_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* v_cfg_1807_){
_start:
{
lean_object* v___f_1808_; lean_object* v___x_1809_; 
v___f_1808_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__0));
v___x_1809_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1807_, v___f_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(lean_object* v_g_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___closed__0));
v___x_1821_ = l_Lean_MVarId_constructor(v_g_1814_, v___x_1820_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1830_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1830_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_a_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1826_);
v___x_1828_ = v___x_1824_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1831_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1821_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1821_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0___boxed(lean_object* v_g_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lam__0(v_g_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* v_cfg_1847_){
_start:
{
lean_object* v___f_1848_; lean_object* v___x_1849_; 
v___f_1848_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__0));
v___x_1849_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1847_, v___f_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(lean_object* v_g_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
lean_inc(v_g_1852_);
v___x_1858_ = l_Lean_MVarId_getType(v_g_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = lean_box(0);
v___x_1861_ = l_Lean_Meta_synthInstance(v_a_1859_, v___x_1860_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = l_Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0___redArg(v_g_1852_, v_a_1862_, v___y_1854_);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1863_, 0);
lean_dec(v_unused_1872_);
v___x_1865_ = v___x_1863_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v___x_1863_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___closed__0));
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_g_1852_);
v_a_1873_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1861_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1861_);
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
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_g_1852_);
v_a_1881_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1858_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1858_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0___boxed(lean_object* v_g_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lam__0(v_g_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* v_cfg_1897_){
_start:
{
lean_object* v___f_1898_; lean_object* v___x_1899_; 
v___f_1898_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__0));
v___x_1899_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v_cfg_1897_, v___f_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(lean_object* v_e_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Lean_Expr_hasMVar(v_e_1900_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_e_1900_);
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; lean_object* v_mctx_1906_; lean_object* v___x_1907_; lean_object* v_fst_1908_; lean_object* v_snd_1909_; lean_object* v___x_1910_; lean_object* v_cache_1911_; lean_object* v_zetaDeltaFVarIds_1912_; lean_object* v_postponed_1913_; lean_object* v_diag_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1923_; 
v___x_1905_ = lean_st_ref_get(v___y_1901_);
v_mctx_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc_ref(v_mctx_1906_);
lean_dec(v___x_1905_);
v___x_1907_ = l_Lean_instantiateMVarsCore(v_mctx_1906_, v_e_1900_);
v_fst_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_fst_1908_);
v_snd_1909_ = lean_ctor_get(v___x_1907_, 1);
lean_inc(v_snd_1909_);
lean_dec_ref(v___x_1907_);
v___x_1910_ = lean_st_ref_take(v___y_1901_);
v_cache_1911_ = lean_ctor_get(v___x_1910_, 1);
v_zetaDeltaFVarIds_1912_ = lean_ctor_get(v___x_1910_, 2);
v_postponed_1913_ = lean_ctor_get(v___x_1910_, 3);
v_diag_1914_ = lean_ctor_get(v___x_1910_, 4);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___x_1910_, 0);
lean_dec(v_unused_1924_);
v___x_1916_ = v___x_1910_;
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_diag_1914_);
lean_inc(v_postponed_1913_);
lean_inc(v_zetaDeltaFVarIds_1912_);
lean_inc(v_cache_1911_);
lean_dec(v___x_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v_snd_1909_);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_snd_1909_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_cache_1911_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_zetaDeltaFVarIds_1912_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_postponed_1913_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_diag_1914_);
v___x_1919_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_st_ref_set(v___y_1901_, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_fst_1908_);
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg___boxed(lean_object* v_e_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1925_, v___y_1926_);
lean_dec(v___y_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(lean_object* v_e_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___redArg(v_e_1929_, v___y_1931_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed(lean_object* v_e_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0(v_e_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(lean_object* v_mvarId_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1943_, v_x_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1950_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1950_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg___boxed(lean_object* v_mvarId_1967_, lean_object* v_x_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1967_, v_x_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(lean_object* v_00_u03b1_1975_, lean_object* v_mvarId_1976_, lean_object* v_x_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_mvarId_1976_, v_x_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___boxed(lean_object* v_00_u03b1_1984_, lean_object* v_mvarId_1985_, lean_object* v_x_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1(v_00_u03b1_1984_, v_mvarId_1985_, v_x_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(lean_object* v_msg_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_ref_1999_; lean_object* v___x_2000_; lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_ref_1999_ = lean_ctor_get(v___y_1996_, 5);
v___x_2000_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4_spec__5_spec__8(v_msg_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
lean_inc(v_ref_1999_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_ref_1999_);
lean_ctor_set(v___x_2005_, 1, v_a_2001_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 1);
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg___boxed(lean_object* v_msg_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(lean_object* v_x_2017_, lean_object* v_x_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = l_List_reverse___redArg(v_x_2018_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v_head_2026_; lean_object* v_tail_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2047_; 
v_head_2026_ = lean_ctor_get(v_x_2017_, 0);
v_tail_2027_ = lean_ctor_get(v_x_2017_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_x_2017_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2029_ = v_x_2017_;
v_isShared_2030_ = v_isSharedCheck_2047_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_tail_2027_);
lean_inc(v_head_2026_);
lean_dec(v_x_2017_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2047_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_inc(v_head_2026_);
v___x_2031_ = l_Lean_Expr_mvar___override(v_head_2026_);
v___x_2032_ = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__0___boxed), 6, 1);
lean_closure_set(v___x_2032_, 0, v___x_2031_);
v___x_2033_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_head_2026_, v___x_2032_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v_x_2018_);
lean_ctor_set(v___x_2029_, 0, v_a_2034_);
v___x_2036_ = v___x_2029_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2034_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_x_2018_);
v___x_2036_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v_x_2017_ = v_tail_2027_;
v_x_2018_ = v___x_2036_;
goto _start;
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_del_object(v___x_2029_);
lean_dec(v_tail_2027_);
lean_dec(v_x_2018_);
v_a_2039_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2033_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2033_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2___boxed(lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_x_2048_, v_x_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2055_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__0));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(lean_object* v_test_2059_, lean_object* v_proc_2060_, lean_object* v_orig_2061_, lean_object* v_goals_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_box(0);
lean_inc(v_orig_2061_);
v___x_2069_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__2(v_orig_2061_, v___x_2068_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v___y_2064_);
lean_inc_ref(v___y_2063_);
v___x_2071_ = lean_apply_6(v_test_2059_, v_a_2070_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, lean_box(0));
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; uint8_t v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = lean_unbox(v_a_2072_);
lean_dec(v_a_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_goals_2062_);
lean_dec(v_orig_2061_);
lean_dec_ref(v_proc_2060_);
v___x_2074_ = lean_obj_once(&l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1, &l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___closed__1);
v___x_2075_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2074_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v___x_2084_; 
lean_inc(v___y_2066_);
lean_inc_ref(v___y_2065_);
lean_inc(v___y_2064_);
lean_inc_ref(v___y_2063_);
v___x_2084_ = lean_apply_7(v_proc_2060_, v_orig_2061_, v_goals_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, lean_box(0));
return v___x_2084_;
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_goals_2062_);
lean_dec(v_orig_2061_);
lean_dec_ref(v_proc_2060_);
v_a_2085_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2071_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2071_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_goals_2062_);
lean_dec(v_orig_2061_);
lean_dec_ref(v_proc_2060_);
lean_dec_ref(v_test_2059_);
v_a_2093_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2069_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2069_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed(lean_object* v_test_2101_, lean_object* v_proc_2102_, lean_object* v_orig_2103_, lean_object* v_goals_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0(v_test_2101_, v_proc_2102_, v_orig_2103_, v_goals_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* v_cfg_2111_, lean_object* v_test_2112_){
_start:
{
lean_object* v_toApplyRulesConfig_2113_; lean_object* v_toBacktrackConfig_2114_; uint8_t v_backtracking_2115_; uint8_t v_intro_2116_; uint8_t v_constructor_2117_; uint8_t v_suggestions_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2150_; 
v_toApplyRulesConfig_2113_ = lean_ctor_get(v_cfg_2111_, 0);
lean_inc_ref(v_toApplyRulesConfig_2113_);
v_toBacktrackConfig_2114_ = lean_ctor_get(v_toApplyRulesConfig_2113_, 0);
lean_inc_ref(v_toBacktrackConfig_2114_);
v_backtracking_2115_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*1);
v_intro_2116_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*1 + 1);
v_constructor_2117_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*1 + 2);
v_suggestions_2118_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*1 + 3);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_cfg_2111_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_cfg_2111_, 0);
lean_dec(v_unused_2151_);
v___x_2120_ = v_cfg_2111_;
v_isShared_2121_ = v_isSharedCheck_2150_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v_cfg_2111_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2150_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_toApplyConfig_2122_; uint8_t v_transparency_2123_; uint8_t v_symm_2124_; uint8_t v_exfalso_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2148_; 
v_toApplyConfig_2122_ = lean_ctor_get(v_toApplyRulesConfig_2113_, 1);
v_transparency_2123_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2113_, sizeof(void*)*2);
v_symm_2124_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2113_, sizeof(void*)*2 + 1);
v_exfalso_2125_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2113_, sizeof(void*)*2 + 2);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_toApplyRulesConfig_2113_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v_toApplyRulesConfig_2113_, 0);
lean_dec(v_unused_2149_);
v___x_2127_ = v_toApplyRulesConfig_2113_;
v_isShared_2128_ = v_isSharedCheck_2148_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_toApplyConfig_2122_);
lean_dec(v_toApplyRulesConfig_2113_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2148_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_maxDepth_2129_; lean_object* v_proc_2130_; lean_object* v_suspend_2131_; lean_object* v_discharge_2132_; uint8_t v_commitIndependentGoals_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_maxDepth_2129_ = lean_ctor_get(v_toBacktrackConfig_2114_, 0);
v_proc_2130_ = lean_ctor_get(v_toBacktrackConfig_2114_, 1);
v_suspend_2131_ = lean_ctor_get(v_toBacktrackConfig_2114_, 2);
v_discharge_2132_ = lean_ctor_get(v_toBacktrackConfig_2114_, 3);
v_commitIndependentGoals_2133_ = lean_ctor_get_uint8(v_toBacktrackConfig_2114_, sizeof(void*)*4);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_toBacktrackConfig_2114_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2135_ = v_toBacktrackConfig_2114_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_discharge_2132_);
lean_inc(v_suspend_2131_);
lean_inc(v_proc_2130_);
lean_inc(v_maxDepth_2129_);
lean_dec(v_toBacktrackConfig_2114_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___f_2137_; lean_object* v___x_2139_; 
v___f_2137_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2137_, 0, v_test_2112_);
lean_closure_set(v___f_2137_, 1, v_proc_2130_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v___f_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_maxDepth_2129_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___f_2137_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_suspend_2131_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_discharge_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2146_, sizeof(void*)*4, v_commitIndependentGoals_2133_);
v___x_2139_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2139_);
v___x_2141_ = v___x_2127_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_toApplyConfig_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*2, v_transparency_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*2 + 1, v_symm_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2145_, sizeof(void*)*2 + 2, v_exfalso_2125_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2141_);
v___x_2143_ = v___x_2120_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2144_, sizeof(void*)*1, v_backtracking_2115_);
lean_ctor_set_uint8(v_reuseFailAlloc_2144_, sizeof(void*)*1 + 1, v_intro_2116_);
lean_ctor_set_uint8(v_reuseFailAlloc_2144_, sizeof(void*)*1 + 2, v_constructor_2117_);
lean_ctor_set_uint8(v_reuseFailAlloc_2144_, sizeof(void*)*1 + 3, v_suggestions_2118_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(lean_object* v_00_u03b1_2152_, lean_object* v_msg_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v_msg_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_msg_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3(v_00_u03b1_2160_, v_msg_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(lean_object* v_test_2169_, lean_object* v_sols_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___closed__0));
lean_inc(v_sols_2170_);
v___x_2177_ = l_List_any___redArg(v_sols_2170_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_inc(v___y_2174_);
lean_inc_ref(v___y_2173_);
lean_inc(v___y_2172_);
lean_inc_ref(v___y_2171_);
v___x_2178_ = lean_apply_6(v_test_2169_, v_sols_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, lean_box(0));
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v_sols_2170_);
lean_dec_ref(v_test_2169_);
v___x_2179_ = lean_box(v___x_2177_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed(lean_object* v_test_2181_, lean_object* v_sols_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0(v_test_2181_, v_sols_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* v_cfg_2189_, lean_object* v_test_2190_){
_start:
{
lean_object* v___f_2191_; lean_object* v___x_2192_; 
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2191_, 0, v_test_2190_);
v___x_2192_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(v_cfg_2189_, v___f_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(lean_object* v_e_2193_, lean_object* v_s_2194_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = l_Lean_Expr_occurs(v_e_2193_, v_s_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed(lean_object* v_e_2196_, lean_object* v_s_2197_){
_start:
{
uint8_t v_res_2198_; lean_object* v_r_2199_; 
v_res_2198_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0(v_e_2196_, v_s_2197_);
lean_dec_ref(v_s_2197_);
v_r_2199_ = lean_box(v_res_2198_);
return v_r_2199_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(lean_object* v_sols_2200_, lean_object* v_e_2201_){
_start:
{
lean_object* v___f_2202_; uint8_t v___x_2203_; 
v___f_2202_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2202_, 0, v_e_2201_);
v___x_2203_ = l_List_any___redArg(v_sols_2200_, v___f_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed(lean_object* v_sols_2204_, lean_object* v_e_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1(v_sols_2204_, v_e_2205_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(lean_object* v_use_2208_, lean_object* v_sols_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___f_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2215_, 0, v_sols_2209_);
v___x_2216_ = l_List_all___redArg(v_use_2208_, v___f_2215_);
v___x_2217_ = lean_box(v___x_2216_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed(lean_object* v_use_2219_, lean_object* v_sols_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2(v_use_2219_, v_sols_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* v_cfg_2227_, lean_object* v_use_2228_){
_start:
{
lean_object* v___f_2229_; lean_object* v___x_2230_; 
v___f_2229_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2229_, 0, v_use_2228_);
v___x_2230_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(v_cfg_2227_, v___f_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* v_cfg_2231_){
_start:
{
lean_object* v___y_2233_; lean_object* v_toApplyRulesConfig_2234_; uint8_t v_backtracking_2235_; uint8_t v_intro_2236_; uint8_t v_constructor_2237_; uint8_t v_suggestions_2238_; uint8_t v_intro_2242_; 
v_intro_2242_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1 + 1);
if (v_intro_2242_ == 0)
{
lean_object* v_toApplyRulesConfig_2243_; uint8_t v_backtracking_2244_; uint8_t v_constructor_2245_; uint8_t v_suggestions_2246_; 
v_toApplyRulesConfig_2243_ = lean_ctor_get(v_cfg_2231_, 0);
lean_inc_ref(v_toApplyRulesConfig_2243_);
v_backtracking_2244_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1);
v_constructor_2245_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1 + 2);
v_suggestions_2246_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1 + 3);
v___y_2233_ = v_cfg_2231_;
v_toApplyRulesConfig_2234_ = v_toApplyRulesConfig_2243_;
v_backtracking_2235_ = v_backtracking_2244_;
v_intro_2236_ = v_intro_2242_;
v_constructor_2237_ = v_constructor_2245_;
v_suggestions_2238_ = v_suggestions_2246_;
goto v___jp_2232_;
}
else
{
lean_object* v_toApplyRulesConfig_2247_; uint8_t v_backtracking_2248_; uint8_t v_constructor_2249_; uint8_t v_suggestions_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2264_; 
v_toApplyRulesConfig_2247_ = lean_ctor_get(v_cfg_2231_, 0);
v_backtracking_2248_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1);
v_constructor_2249_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1 + 2);
v_suggestions_2250_ = lean_ctor_get_uint8(v_cfg_2231_, sizeof(void*)*1 + 3);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_cfg_2231_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2252_ = v_cfg_2231_;
v_isShared_2253_ = v_isSharedCheck_2264_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_toApplyRulesConfig_2247_);
lean_dec(v_cfg_2231_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2264_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
uint8_t v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = 0;
if (v_isShared_2253_ == 0)
{
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_toApplyRulesConfig_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2263_, sizeof(void*)*1, v_backtracking_2248_);
lean_ctor_set_uint8(v_reuseFailAlloc_2263_, sizeof(void*)*1 + 2, v_constructor_2249_);
lean_ctor_set_uint8(v_reuseFailAlloc_2263_, sizeof(void*)*1 + 3, v_suggestions_2250_);
v___x_2256_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; lean_object* v_toApplyRulesConfig_2258_; uint8_t v_backtracking_2259_; uint8_t v_intro_2260_; uint8_t v_constructor_2261_; uint8_t v_suggestions_2262_; 
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*1 + 1, v___x_2254_);
v___x_2257_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(v___x_2256_);
v_toApplyRulesConfig_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc_ref(v_toApplyRulesConfig_2258_);
v_backtracking_2259_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*1);
v_intro_2260_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*1 + 1);
v_constructor_2261_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*1 + 2);
v_suggestions_2262_ = lean_ctor_get_uint8(v___x_2257_, sizeof(void*)*1 + 3);
v___y_2233_ = v___x_2257_;
v_toApplyRulesConfig_2234_ = v_toApplyRulesConfig_2258_;
v_backtracking_2235_ = v_backtracking_2259_;
v_intro_2236_ = v_intro_2260_;
v_constructor_2237_ = v_constructor_2261_;
v_suggestions_2238_ = v_suggestions_2262_;
goto v___jp_2232_;
}
}
}
v___jp_2232_:
{
if (v_constructor_2237_ == 0)
{
lean_dec_ref(v_toApplyRulesConfig_2234_);
return v___y_2233_;
}
else
{
uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec_ref(v___y_2233_);
v___x_2239_ = 0;
v___x_2240_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2240_, 0, v_toApplyRulesConfig_2234_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1, v_backtracking_2235_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1 + 1, v_intro_2236_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1 + 2, v___x_2239_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1 + 3, v_suggestions_2238_);
v___x_2241_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(v___x_2240_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = l_List_reverse___redArg(v_x_2266_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
return v___x_2275_;
}
else
{
lean_object* v_head_2276_; lean_object* v_tail_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2295_; 
v_head_2276_ = lean_ctor_get(v_x_2265_, 0);
v_tail_2277_ = lean_ctor_get(v_x_2265_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2279_ = v_x_2265_;
v_isShared_2280_ = v_isSharedCheck_2295_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_tail_2277_);
lean_inc(v_head_2276_);
lean_dec(v_x_2265_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2295_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; 
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
v___x_2281_ = lean_apply_7(v_head_2276_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, lean_box(0));
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2281_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v_x_2266_);
lean_ctor_set(v___x_2279_, 0, v_a_2282_);
v___x_2284_ = v___x_2279_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2282_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_x_2266_);
v___x_2284_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
v_x_2265_ = v_tail_2277_;
v_x_2266_ = v___x_2284_;
goto _start;
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_del_object(v___x_2279_);
lean_dec(v_tail_2277_);
lean_dec(v_x_2266_);
v_a_2287_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2281_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2281_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0___boxed(lean_object* v_x_2296_, lean_object* v_x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_x_2296_, v_x_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(lean_object* v_ctx_2306_, lean_object* v_cfg_2307_, lean_object* v_lemmas_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v___y_2312_);
lean_inc_ref(v___y_2311_);
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
v___x_2316_ = lean_apply_8(v_ctx_2306_, v_cfg_2307_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, lean_box(0));
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = lean_box(0);
v___x_2319_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_elabContextLemmas_spec__0(v_lemmas_2308_, v___x_2318_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2328_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = l_List_appendTR___redArg(v_a_2317_, v_a_2320_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2324_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_dec(v_a_2317_);
return v___x_2319_;
}
}
else
{
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v_lemmas_2308_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed(lean_object* v_ctx_2329_, lean_object* v_cfg_2330_, lean_object* v_lemmas_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0(v_ctx_2329_, v_cfg_2330_, v_lemmas_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(lean_object* v_x_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = 0;
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1___boxed(lean_object* v_x_2342_){
_start:
{
uint8_t v_res_2343_; lean_object* v_r_2344_; 
v_res_2343_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__1(v_x_2342_);
lean_dec(v_x_2342_);
v_r_2344_ = lean_box(v_res_2343_);
return v_r_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(lean_object* v___f_2345_, lean_object* v___x_2346_, lean_object* v___x_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_2345_, v___x_2346_, v___x_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2362_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_fst_2358_; lean_object* v___x_2360_; 
v_fst_2358_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_fst_2358_);
lean_dec(v_a_2354_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v_fst_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2353_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2353_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed(lean_object* v___f_2371_, lean_object* v___x_2372_, lean_object* v___x_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2(v___f_2371_, v___x_2372_, v___x_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* v_cfg_2394_, lean_object* v_g_2395_, lean_object* v_lemmas_2396_, lean_object* v_ctx_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; 
v___f_2403_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2403_, 0, v_ctx_2397_);
lean_closure_set(v___f_2403_, 1, v_cfg_2394_);
lean_closure_set(v___f_2403_, 2, v_lemmas_2396_);
v___x_2404_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2));
v___x_2405_ = ((lean_object*)(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3));
v___f_2406_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lam__2___boxed), 8, 3);
lean_closure_set(v___f_2406_, 0, v___f_2403_);
lean_closure_set(v___f_2406_, 1, v___x_2404_);
lean_closure_set(v___f_2406_, 2, v___x_2405_);
v___x_2407_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__1___redArg(v_g_2395_, v___f_2406_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___boxed(lean_object* v_cfg_2408_, lean_object* v_g_2409_, lean_object* v_lemmas_2410_, lean_object* v_ctx_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2408_, v_g_2409_, v_lemmas_2410_, v_ctx_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* v_cfg_2418_, lean_object* v_lemmas_2419_, lean_object* v_ctx_2420_, lean_object* v_g_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; 
lean_inc(v_g_2421_);
lean_inc_ref(v_cfg_2418_);
v___x_2427_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2418_, v_g_2421_, v_lemmas_2419_, v_ctx_2420_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_toApplyRulesConfig_2428_; lean_object* v_a_2429_; lean_object* v_toApplyConfig_2430_; uint8_t v_transparency_2431_; lean_object* v___x_2432_; 
v_toApplyRulesConfig_2428_ = lean_ctor_get(v_cfg_2418_, 0);
lean_inc_ref(v_toApplyRulesConfig_2428_);
lean_dec_ref(v_cfg_2418_);
v_a_2429_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2427_);
v_toApplyConfig_2430_ = lean_ctor_get(v_toApplyRulesConfig_2428_, 1);
lean_inc_ref(v_toApplyConfig_2430_);
v_transparency_2431_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2428_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2428_);
v___x_2432_ = l_Lean_Meta_SolveByElim_applyTactics___redArg(v_toApplyConfig_2430_, v_transparency_2431_, v_a_2429_, v_g_2421_, v_a_2423_, v_a_2425_);
return v___x_2432_;
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_g_2421_);
lean_dec_ref(v_cfg_2418_);
v_a_2433_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2427_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2427_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas___boxed(lean_object* v_cfg_2441_, lean_object* v_lemmas_2442_, lean_object* v_ctx_2443_, lean_object* v_g_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Meta_SolveByElim_applyLemmas(v_cfg_2441_, v_lemmas_2442_, v_ctx_2443_, v_g_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* v_cfg_2451_, lean_object* v_lemmas_2452_, lean_object* v_ctx_2453_, lean_object* v_g_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; 
lean_inc(v_g_2454_);
lean_inc_ref(v_cfg_2451_);
v___x_2460_ = l_Lean_Meta_SolveByElim_elabContextLemmas(v_cfg_2451_, v_g_2454_, v_lemmas_2452_, v_ctx_2453_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_toApplyRulesConfig_2461_; lean_object* v_a_2462_; lean_object* v_toApplyConfig_2463_; uint8_t v_transparency_2464_; lean_object* v___x_2465_; 
v_toApplyRulesConfig_2461_ = lean_ctor_get(v_cfg_2451_, 0);
lean_inc_ref(v_toApplyRulesConfig_2461_);
lean_dec_ref(v_cfg_2451_);
v_a_2462_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v___x_2460_);
v_toApplyConfig_2463_ = lean_ctor_get(v_toApplyRulesConfig_2461_, 1);
lean_inc_ref(v_toApplyConfig_2463_);
v_transparency_2464_ = lean_ctor_get_uint8(v_toApplyRulesConfig_2461_, sizeof(void*)*2);
lean_dec_ref(v_toApplyRulesConfig_2461_);
v___x_2465_ = l_Lean_Meta_SolveByElim_applyFirst(v_toApplyConfig_2463_, v_transparency_2464_, v_a_2462_, v_g_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2465_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_g_2454_);
lean_dec_ref(v_cfg_2451_);
v_a_2466_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2460_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2460_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma___boxed(lean_object* v_cfg_2474_, lean_object* v_lemmas_2475_, lean_object* v_ctx_2476_, lean_object* v_g_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_SolveByElim_applyFirstLemma(v_cfg_2474_, v_lemmas_2475_, v_ctx_2476_, v_g_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_keys_2484_, lean_object* v_i_2485_, lean_object* v_k_2486_){
_start:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = lean_array_get_size(v_keys_2484_);
v___x_2488_ = lean_nat_dec_lt(v_i_2485_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_dec(v_i_2485_);
return v___x_2488_;
}
else
{
lean_object* v_k_x27_2489_; uint8_t v___x_2490_; 
v_k_x27_2489_ = lean_array_fget_borrowed(v_keys_2484_, v_i_2485_);
v___x_2490_ = l_Lean_instBEqMVarId_beq(v_k_2486_, v_k_x27_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_add(v_i_2485_, v___x_2491_);
lean_dec(v_i_2485_);
v_i_2485_ = v___x_2492_;
goto _start;
}
else
{
lean_dec(v_i_2485_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_keys_2494_, lean_object* v_i_2495_, lean_object* v_k_2496_){
_start:
{
uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_res_2497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2494_, v_i_2495_, v_k_2496_);
lean_dec(v_k_2496_);
lean_dec_ref(v_keys_2494_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2499_, size_t v_x_2500_, lean_object* v_x_2501_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
lean_object* v_es_2502_; lean_object* v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; lean_object* v_j_2507_; lean_object* v___x_2508_; 
v_es_2502_ = lean_ctor_get(v_x_2499_, 0);
lean_inc_ref(v_es_2502_);
lean_dec_ref(v_x_2499_);
v___x_2503_ = lean_box(2);
v___x_2504_ = ((size_t)5ULL);
v___x_2505_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2506_ = lean_usize_land(v_x_2500_, v___x_2505_);
v_j_2507_ = lean_usize_to_nat(v___x_2506_);
v___x_2508_ = lean_array_get(v___x_2503_, v_es_2502_, v_j_2507_);
lean_dec(v_j_2507_);
lean_dec_ref(v_es_2502_);
switch(lean_obj_tag(v___x_2508_))
{
case 0:
{
lean_object* v_key_2509_; uint8_t v___x_2510_; 
v_key_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_key_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = l_Lean_instBEqMVarId_beq(v_x_2501_, v_key_2509_);
lean_dec(v_key_2509_);
return v___x_2510_;
}
case 1:
{
lean_object* v_node_2511_; size_t v___x_2512_; 
v_node_2511_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_node_2511_);
lean_dec_ref(v___x_2508_);
v___x_2512_ = lean_usize_shift_right(v_x_2500_, v___x_2504_);
v_x_2499_ = v_node_2511_;
v_x_2500_ = v___x_2512_;
goto _start;
}
default: 
{
uint8_t v___x_2514_; 
v___x_2514_ = 0;
return v___x_2514_;
}
}
}
else
{
lean_object* v_ks_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_ks_2515_ = lean_ctor_get(v_x_2499_, 0);
lean_inc_ref(v_ks_2515_);
lean_dec_ref(v_x_2499_);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_ks_2515_, v___x_2516_, v_x_2501_);
lean_dec_ref(v_ks_2515_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
size_t v_x_2218__boxed_2521_; uint8_t v_res_2522_; lean_object* v_r_2523_; 
v_x_2218__boxed_2521_ = lean_unbox_usize(v_x_2519_);
lean_dec(v_x_2519_);
v_res_2522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2518_, v_x_2218__boxed_2521_, v_x_2520_);
lean_dec(v_x_2520_);
v_r_2523_ = lean_box(v_res_2522_);
return v_r_2523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
uint64_t v___x_2526_; size_t v___x_2527_; uint8_t v___x_2528_; 
v___x_2526_ = l_Lean_instHashableMVarId_hash(v_x_2525_);
v___x_2527_ = lean_uint64_to_usize(v___x_2526_);
v___x_2528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2524_, v___x_2527_, v_x_2525_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2529_, lean_object* v_x_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2529_, v_x_2530_);
lean_dec(v_x_2530_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(lean_object* v_mvarId_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v_mctx_2537_; lean_object* v_eAssignment_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2536_ = lean_st_ref_get(v___y_2534_);
v_mctx_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_mctx_2537_);
lean_dec(v___x_2536_);
v_eAssignment_2538_ = lean_ctor_get(v_mctx_2537_, 7);
lean_inc_ref(v_eAssignment_2538_);
lean_dec_ref(v_mctx_2537_);
v___x_2539_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_eAssignment_2538_, v_mvarId_2533_);
v___x_2540_ = lean_box(v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_mvarId_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec(v_mvarId_2542_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2546_, lean_object* v_x_2547_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 0)
{
return v_x_2546_;
}
else
{
lean_object* v_head_2548_; lean_object* v_tail_2549_; lean_object* v___x_2550_; 
v_head_2548_ = lean_ctor_get(v_x_2547_, 0);
lean_inc(v_head_2548_);
v_tail_2549_ = lean_ctor_get(v_x_2547_, 1);
lean_inc(v_tail_2549_);
lean_dec_ref(v_x_2547_);
v___x_2550_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_x_2546_, v_head_2548_);
v_x_2546_ = v___x_2550_;
v_x_2547_ = v_tail_2549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(lean_object* v_f_2552_, lean_object* v_a_2553_, uint8_t v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
if (lean_obj_tag(v_a_2555_) == 0)
{
if (lean_obj_tag(v_a_2556_) == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_a_2553_);
lean_dec_ref(v_f_2552_);
v___x_2563_ = lean_box(v_a_2554_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v_a_2557_);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
else
{
lean_object* v_head_2566_; lean_object* v_tail_2567_; 
v_head_2566_ = lean_ctor_get(v_a_2556_, 0);
lean_inc(v_head_2566_);
v_tail_2567_ = lean_ctor_get(v_a_2556_, 1);
lean_inc(v_tail_2567_);
lean_dec_ref(v_a_2556_);
v_a_2555_ = v_head_2566_;
v_a_2556_ = v_tail_2567_;
goto _start;
}
}
else
{
lean_object* v_head_2569_; lean_object* v_tail_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2613_; 
v_head_2569_ = lean_ctor_get(v_a_2555_, 0);
v_tail_2570_ = lean_ctor_get(v_a_2555_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2572_ = v_a_2555_;
v_isShared_2573_ = v_isSharedCheck_2613_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_tail_2570_);
lean_inc(v_head_2569_);
lean_dec(v_a_2555_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2613_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2612_; 
v___x_2574_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_head_2569_, v___y_2559_);
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2612_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2612_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
if (v___x_2579_ == 0)
{
lean_object* v_zero_2580_; uint8_t v_isZero_2581_; 
v_zero_2580_ = lean_unsigned_to_nat(0u);
v_isZero_2581_ = lean_nat_dec_eq(v_a_2553_, v_zero_2580_);
if (v_isZero_2581_ == 1)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
lean_del_object(v___x_2572_);
lean_dec(v_a_2553_);
lean_dec_ref(v_f_2552_);
v___x_2582_ = lean_array_push(v_a_2557_, v_head_2569_);
v___x_2583_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_2582_, v_tail_2570_);
v___x_2584_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1_spec__2(v___x_2583_, v_a_2556_);
v___x_2585_ = lean_box(v_a_2554_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___x_2584_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2586_);
v___x_2588_ = v___x_2577_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2577_);
lean_inc_ref(v_f_2552_);
lean_inc(v_head_2569_);
v___x_2590_ = lean_apply_1(v_f_2552_, v_head_2569_);
v___x_2591_ = l_Lean_observing_x3f___at___00Lean_Meta_SolveByElim_applyTactics_spec__7___redArg(v___x_2590_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_one_2593_; lean_object* v_n_2594_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
v_one_2593_ = lean_unsigned_to_nat(1u);
v_n_2594_ = lean_nat_sub(v_a_2553_, v_one_2593_);
lean_dec(v_a_2553_);
if (lean_obj_tag(v_a_2592_) == 0)
{
lean_object* v___x_2595_; 
lean_del_object(v___x_2572_);
v___x_2595_ = lean_array_push(v_a_2557_, v_head_2569_);
v_a_2553_ = v_n_2594_;
v_a_2555_ = v_tail_2570_;
v_a_2557_ = v___x_2595_;
goto _start;
}
else
{
lean_object* v_val_2597_; uint8_t v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v_head_2569_);
v_val_2597_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_val_2597_);
lean_dec_ref(v_a_2592_);
v___x_2598_ = 1;
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 1, v_a_2556_);
lean_ctor_set(v___x_2572_, 0, v_tail_2570_);
v___x_2600_ = v___x_2572_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_tail_2570_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_a_2556_);
v___x_2600_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
v_a_2553_ = v_n_2594_;
v_a_2554_ = v___x_2598_;
v_a_2555_ = v_val_2597_;
v_a_2556_ = v___x_2600_;
goto _start;
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_del_object(v___x_2572_);
lean_dec(v_tail_2570_);
lean_dec(v_head_2569_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec(v_a_2553_);
lean_dec_ref(v_f_2552_);
v_a_2603_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2591_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2591_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
else
{
lean_del_object(v___x_2577_);
lean_del_object(v___x_2572_);
lean_dec(v_head_2569_);
v_a_2555_ = v_tail_2570_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v_a_2299__boxed_2625_; lean_object* v_res_2626_; 
v_a_2299__boxed_2625_ = lean_unbox(v_a_2616_);
v_res_2626_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2614_, v_a_2615_, v_a_2299__boxed_2625_, v_a_2617_, v_a_2618_, v_a_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(lean_object* v_as_2627_, size_t v_i_2628_, size_t v_stop_2629_, lean_object* v_b_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_a_2637_; uint8_t v___x_2641_; 
v___x_2641_ = lean_usize_dec_eq(v_i_2628_, v_stop_2629_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2645_; 
v___x_2642_ = lean_array_uget_borrowed(v_as_2627_, v_i_2628_);
v___x_2645_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v___x_2642_, v___y_2632_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; uint8_t v___x_2647_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = lean_unbox(v_a_2646_);
lean_dec(v_a_2646_);
if (v___x_2647_ == 0)
{
goto v___jp_2643_;
}
else
{
v_a_2637_ = v_b_2630_;
goto v___jp_2636_;
}
}
else
{
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2648_; uint8_t v___x_2649_; 
v_a_2648_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2645_);
v___x_2649_ = lean_unbox(v_a_2648_);
lean_dec(v_a_2648_);
if (v___x_2649_ == 0)
{
v_a_2637_ = v_b_2630_;
goto v___jp_2636_;
}
else
{
goto v___jp_2643_;
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v_b_2630_);
v_a_2650_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2645_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2645_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
v___jp_2643_:
{
lean_object* v___x_2644_; 
lean_inc(v___x_2642_);
v___x_2644_ = lean_array_push(v_b_2630_, v___x_2642_);
v_a_2637_ = v___x_2644_;
goto v___jp_2636_;
}
}
else
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_b_2630_);
return v___x_2658_;
}
v___jp_2636_:
{
size_t v___x_2638_; size_t v___x_2639_; 
v___x_2638_ = ((size_t)1ULL);
v___x_2639_ = lean_usize_add(v_i_2628_, v___x_2638_);
v_i_2628_ = v___x_2639_;
v_b_2630_ = v_a_2637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3___boxed(lean_object* v_as_2659_, lean_object* v_i_2660_, lean_object* v_stop_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
size_t v_i_boxed_2668_; size_t v_stop_boxed_2669_; lean_object* v_res_2670_; 
v_i_boxed_2668_ = lean_unbox_usize(v_i_2660_);
lean_dec(v_i_2660_);
v_stop_boxed_2669_ = lean_unbox_usize(v_stop_2661_);
lean_dec(v_stop_2661_);
v_res_2670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_as_2659_, v_i_boxed_2668_, v_stop_boxed_2669_, v_b_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_as_2659_);
return v_res_2670_;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2674_ = lean_array_to_list(v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(lean_object* v_f_2675_, lean_object* v_goals_2676_, lean_object* v_maxIters_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2683_ = 0;
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = ((lean_object*)(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__0));
v___x_2687_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__1(v_f_2675_, v_maxIters_2677_, v___x_2683_, v_goals_2676_, v___x_2684_, v___x_2686_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2737_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2737_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2737_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_fst_2692_; lean_object* v_snd_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2736_; 
v_fst_2692_ = lean_ctor_get(v_a_2688_, 0);
v_snd_2693_ = lean_ctor_get(v_a_2688_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2695_ = v_a_2688_;
v_isShared_2696_ = v_isSharedCheck_2736_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_snd_2693_);
lean_inc(v_fst_2692_);
lean_dec(v_a_2688_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2736_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_____do__lift_2698_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = lean_array_get_size(v_snd_2693_);
v___x_2707_ = lean_nat_dec_lt(v___x_2685_, v___x_2706_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_del_object(v___x_2695_);
lean_dec(v_snd_2693_);
lean_del_object(v___x_2690_);
v___x_2708_ = lean_obj_once(&l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1, &l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1_once, _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___closed__1);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_fst_2692_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
else
{
uint8_t v___x_2711_; 
v___x_2711_ = lean_nat_dec_le(v___x_2706_, v___x_2706_);
if (v___x_2711_ == 0)
{
if (v___x_2707_ == 0)
{
lean_dec(v_snd_2693_);
v_____do__lift_2698_ = v___x_2686_;
goto v___jp_2697_;
}
else
{
size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = lean_usize_of_nat(v___x_2706_);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2693_, v___x_2712_, v___x_2713_, v___x_2686_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v_snd_2693_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2714_);
v_____do__lift_2698_ = v_a_2715_;
goto v___jp_2697_;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_del_object(v___x_2695_);
lean_dec(v_fst_2692_);
lean_del_object(v___x_2690_);
v_a_2716_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2714_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
else
{
size_t v___x_2724_; size_t v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = ((size_t)0ULL);
v___x_2725_ = lean_usize_of_nat(v___x_2706_);
v___x_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__3(v_snd_2693_, v___x_2724_, v___x_2725_, v___x_2686_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v_snd_2693_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2726_);
v_____do__lift_2698_ = v_a_2727_;
goto v___jp_2697_;
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_del_object(v___x_2695_);
lean_dec(v_fst_2692_);
lean_del_object(v___x_2690_);
v_a_2728_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2726_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2726_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
v___jp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = lean_array_to_list(v_____do__lift_2698_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 1, v___x_2699_);
v___x_2701_ = v___x_2695_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_fst_2692_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2703_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2701_);
v___x_2703_ = v___x_2690_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
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
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
v_a_2738_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2687_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2687_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0___boxed(lean_object* v_f_2746_, lean_object* v_goals_2747_, lean_object* v_maxIters_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2746_, v_goals_2747_, v_maxIters_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2754_;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__0));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(lean_object* v_f_2758_, lean_object* v_goals_2759_, lean_object* v_maxIters_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0(v_f_2758_, v_goals_2759_, v_maxIters_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2779_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2779_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2779_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_fst_2771_; uint8_t v___x_2772_; 
v_fst_2771_ = lean_ctor_get(v_a_2767_, 0);
v___x_2772_ = lean_unbox(v_fst_2771_);
if (v___x_2772_ == 1)
{
lean_object* v_snd_2773_; lean_object* v___x_2775_; 
v_snd_2773_ = lean_ctor_get(v_a_2767_, 1);
lean_inc(v_snd_2773_);
lean_dec(v_a_2767_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v_snd_2773_);
v___x_2775_ = v___x_2769_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_snd_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2769_);
lean_dec(v_a_2767_);
v___x_2777_ = lean_obj_once(&l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1, &l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1_once, _init_l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___closed__1);
v___x_2778_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_2777_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2778_;
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
v_a_2780_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2766_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2766_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0___boxed(lean_object* v_f_2788_, lean_object* v_goals_2789_, lean_object* v_maxIters_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v_f_2788_, v_goals_2789_, v_maxIters_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(lean_object* v_lemmas_2797_, lean_object* v_ctx_2798_, lean_object* v_cfg_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
uint8_t v_backtracking_2806_; 
v_backtracking_2806_ = lean_ctor_get_uint8(v_cfg_2799_, sizeof(void*)*1);
if (v_backtracking_2806_ == 0)
{
lean_object* v_toApplyRulesConfig_2807_; lean_object* v_toBacktrackConfig_2808_; lean_object* v_maxDepth_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_toApplyRulesConfig_2807_ = lean_ctor_get(v_cfg_2799_, 0);
v_toBacktrackConfig_2808_ = lean_ctor_get(v_toApplyRulesConfig_2807_, 0);
v_maxDepth_2809_ = lean_ctor_get(v_toBacktrackConfig_2808_, 0);
lean_inc(v_maxDepth_2809_);
v___x_2810_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma___boxed), 9, 3);
lean_closure_set(v___x_2810_, 0, v_cfg_2799_);
lean_closure_set(v___x_2810_, 1, v_lemmas_2797_);
lean_closure_set(v___x_2810_, 2, v_ctx_2798_);
v___x_2811_ = l_Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0(v___x_2810_, v_a_2800_, v_maxDepth_2809_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
return v___x_2811_;
}
else
{
lean_object* v_toApplyRulesConfig_2812_; lean_object* v_toBacktrackConfig_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_toApplyRulesConfig_2812_ = lean_ctor_get(v_cfg_2799_, 0);
v_toBacktrackConfig_2813_ = lean_ctor_get(v_toApplyRulesConfig_2812_, 0);
lean_inc_ref(v_toBacktrackConfig_2813_);
v___x_2814_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_2815_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas___boxed), 9, 3);
lean_closure_set(v___x_2815_, 0, v_cfg_2799_);
lean_closure_set(v___x_2815_, 1, v_lemmas_2797_);
lean_closure_set(v___x_2815_, 2, v_ctx_2798_);
v___x_2816_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_toBacktrackConfig_2813_, v___x_2814_, v___x_2815_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run___boxed(lean_object* v_lemmas_2817_, lean_object* v_ctx_2818_, lean_object* v_cfg_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2817_, v_ctx_2818_, v_cfg_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(lean_object* v_mvarId_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___redArg(v_mvarId_2827_, v___y_2829_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2(v_mvarId_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v_mvarId_2834_);
return v_res_2840_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_){
_start:
{
uint8_t v___x_2844_; 
v___x_2844_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2842_, v_x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
uint8_t v_res_2848_; lean_object* v_r_2849_; 
v_res_2848_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2845_, v_x_2846_, v_x_2847_);
lean_dec(v_x_2847_);
v_r_2849_ = lean_box(v_res_2848_);
return v_r_2849_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2850_, lean_object* v_x_2851_, size_t v_x_2852_, lean_object* v_x_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_2851_, v_x_2852_, v_x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_2855_, lean_object* v_x_2856_, lean_object* v_x_2857_, lean_object* v_x_2858_){
_start:
{
size_t v_x_2759__boxed_2859_; uint8_t v_res_2860_; lean_object* v_r_2861_; 
v_x_2759__boxed_2859_ = lean_unbox_usize(v_x_2857_);
lean_dec(v_x_2857_);
v_res_2860_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5(v_00_u03b2_2855_, v_x_2856_, v_x_2759__boxed_2859_, v_x_2858_);
lean_dec(v_x_2858_);
v_r_2861_ = lean_box(v_res_2860_);
return v_r_2861_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_2862_, lean_object* v_keys_2863_, lean_object* v_vals_2864_, lean_object* v_heq_2865_, lean_object* v_i_2866_, lean_object* v_k_2867_){
_start:
{
uint8_t v___x_2868_; 
v___x_2868_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___redArg(v_keys_2863_, v_i_2866_, v_k_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2869_, lean_object* v_keys_2870_, lean_object* v_vals_2871_, lean_object* v_heq_2872_, lean_object* v_i_2873_, lean_object* v_k_2874_){
_start:
{
uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_res_2875_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat1_x27___at___00__private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run_spec__0_spec__0_spec__2_spec__4_spec__5_spec__7(v_00_u03b2_2869_, v_keys_2870_, v_vals_2871_, v_heq_2872_, v_i_2873_, v_k_2874_);
lean_dec(v_k_2874_);
lean_dec_ref(v_vals_2871_);
lean_dec_ref(v_keys_2870_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__0));
v___x_2879_ = l_Lean_stringToMessageData(v___x_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0(lean_object* v_x_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_obj_once(&l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1, &l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1_once, _init_l_Lean_Meta_SolveByElim_solveByElim___lam__0___closed__1);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lam__0___boxed(lean_object* v_x_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_Meta_SolveByElim_solveByElim___lam__0(v_x_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v_x_2888_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* v_cfg_2896_, lean_object* v_lemmas_2897_, lean_object* v_ctx_2898_, lean_object* v_goals_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_cfg_2905_; lean_object* v___x_2906_; 
v_cfg_2905_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(v_cfg_2896_);
lean_inc(v_goals_2899_);
lean_inc_ref(v_cfg_2905_);
lean_inc_ref(v_ctx_2898_);
lean_inc(v_lemmas_2897_);
v___x_2906_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2897_, v_ctx_2898_, v_cfg_2905_, v_goals_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_dec_ref(v_cfg_2905_);
lean_dec(v_goals_2899_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
return v___x_2906_;
}
else
{
lean_object* v_a_2907_; lean_object* v___f_2908_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; uint8_t v___y_2914_; lean_object* v___y_2915_; uint8_t v___y_2916_; lean_object* v_a_2917_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; lean_object* v___y_2931_; uint8_t v___y_2932_; lean_object* v___y_2933_; lean_object* v_a_2934_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; uint8_t v___y_2941_; lean_object* v___y_2942_; uint8_t v___y_2943_; lean_object* v_a_2944_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; uint8_t v___y_2960_; lean_object* v___y_2961_; uint8_t v___y_2962_; lean_object* v___y_2963_; lean_object* v_a_2964_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; uint8_t v___y_2971_; uint8_t v___y_2972_; lean_object* v___y_2973_; uint8_t v___y_3009_; uint8_t v___x_3064_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
v___f_2908_ = ((lean_object*)(l_Lean_Meta_SolveByElim_solveByElim___closed__0));
v___x_3064_ = l_Lean_Exception_isInterrupt(v_a_2907_);
if (v___x_3064_ == 0)
{
uint8_t v___x_3065_; 
v___x_3065_ = l_Lean_Exception_isRuntime(v_a_2907_);
v___y_3009_ = v___x_3065_;
goto v___jp_3008_;
}
else
{
lean_dec(v_a_2907_);
v___y_3009_ = v___x_3064_;
goto v___jp_3008_;
}
v___jp_2909_:
{
lean_object* v___x_2918_; double v___x_2919_; double v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2918_ = lean_io_get_num_heartbeats();
v___x_2919_ = lean_float_of_nat(v___y_2912_);
v___x_2920_ = lean_float_of_nat(v___x_2918_);
v___x_2921_ = lean_box_float(v___x_2919_);
v___x_2922_ = lean_box_float(v___x_2920_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v_a_2917_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_2910_, v___y_2916_, v___y_2915_, v___y_2911_, v___y_2914_, v___y_2913_, v___f_2908_, v___x_2924_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
return v___x_2925_;
}
v___jp_2926_:
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_a_2934_);
v___y_2910_ = v___y_2927_;
v___y_2911_ = v___y_2928_;
v___y_2912_ = v___y_2929_;
v___y_2913_ = v___y_2931_;
v___y_2914_ = v___y_2930_;
v___y_2915_ = v___y_2933_;
v___y_2916_ = v___y_2932_;
v_a_2917_ = v___x_2935_;
goto v___jp_2909_;
}
v___jp_2936_:
{
lean_object* v___x_2945_; double v___x_2946_; double v___x_2947_; double v___x_2948_; double v___x_2949_; double v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2945_ = lean_io_mono_nanos_now();
v___x_2946_ = lean_float_of_nat(v___y_2939_);
v___x_2947_ = lean_float_once(&l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0, &l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0_once, _init_l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__1___closed__0);
v___x_2948_ = lean_float_div(v___x_2946_, v___x_2947_);
v___x_2949_ = lean_float_of_nat(v___x_2945_);
v___x_2950_ = lean_float_div(v___x_2949_, v___x_2947_);
v___x_2951_ = lean_box_float(v___x_2948_);
v___x_2952_ = lean_box_float(v___x_2950_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v_a_2944_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_SolveByElim_applyTactics_spec__4(v___y_2937_, v___y_2943_, v___y_2942_, v___y_2938_, v___y_2941_, v___y_2940_, v___f_2908_, v___x_2954_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
return v___x_2955_;
}
v___jp_2956_:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_a_2964_);
v___y_2937_ = v___y_2957_;
v___y_2938_ = v___y_2958_;
v___y_2939_ = v___y_2959_;
v___y_2940_ = v___y_2961_;
v___y_2941_ = v___y_2960_;
v___y_2942_ = v___y_2963_;
v___y_2943_ = v___y_2962_;
v_a_2944_ = v___x_2965_;
goto v___jp_2936_;
}
v___jp_2966_:
{
lean_object* v___x_2974_; lean_object* v_a_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_SolveByElim_applyTactics_spec__2___redArg(v_a_2903_);
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref(v___x_2974_);
v___x_2976_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2977_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v___y_2968_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_io_mono_nanos_now();
v___x_2979_ = l_Lean_MVarId_exfalso(v___y_2969_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v_a_2980_);
lean_ctor_set(v___x_2981_, 1, v___y_2970_);
v___x_2982_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2897_, v_ctx_2898_, v_cfg_2905_, v___x_2981_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
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
v___y_2937_ = v___y_2967_;
v___y_2938_ = v___y_2968_;
v___y_2939_ = v___x_2978_;
v___y_2940_ = v_a_2975_;
v___y_2941_ = v___y_2971_;
v___y_2942_ = v___y_2973_;
v___y_2943_ = v___y_2972_;
v_a_2944_ = v___x_2988_;
goto v___jp_2936_;
}
}
}
else
{
lean_object* v_a_2991_; 
v_a_2991_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2982_);
v___y_2957_ = v___y_2967_;
v___y_2958_ = v___y_2968_;
v___y_2959_ = v___x_2978_;
v___y_2960_ = v___y_2971_;
v___y_2961_ = v_a_2975_;
v___y_2962_ = v___y_2972_;
v___y_2963_ = v___y_2973_;
v_a_2964_ = v_a_2991_;
goto v___jp_2956_;
}
}
else
{
lean_object* v_a_2992_; 
lean_dec(v___y_2970_);
lean_dec_ref(v_cfg_2905_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
v_a_2992_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2979_);
v___y_2957_ = v___y_2967_;
v___y_2958_ = v___y_2968_;
v___y_2959_ = v___x_2978_;
v___y_2960_ = v___y_2971_;
v___y_2961_ = v_a_2975_;
v___y_2962_ = v___y_2972_;
v___y_2963_ = v___y_2973_;
v_a_2964_ = v_a_2992_;
goto v___jp_2956_;
}
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_io_get_num_heartbeats();
v___x_2994_ = l_Lean_MVarId_exfalso(v___y_2969_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_a_2995_);
lean_ctor_set(v___x_2996_, 1, v___y_2970_);
v___x_2997_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2897_, v_ctx_2898_, v_cfg_2905_, v___x_2996_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set_tag(v___x_3000_, 1);
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
v___y_2910_ = v___y_2967_;
v___y_2911_ = v___y_2968_;
v___y_2912_ = v___x_2993_;
v___y_2913_ = v_a_2975_;
v___y_2914_ = v___y_2971_;
v___y_2915_ = v___y_2973_;
v___y_2916_ = v___y_2972_;
v_a_2917_ = v___x_3003_;
goto v___jp_2909_;
}
}
}
else
{
lean_object* v_a_3006_; 
v_a_3006_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v___x_2997_);
v___y_2927_ = v___y_2967_;
v___y_2928_ = v___y_2968_;
v___y_2929_ = v___x_2993_;
v___y_2930_ = v___y_2971_;
v___y_2931_ = v_a_2975_;
v___y_2932_ = v___y_2972_;
v___y_2933_ = v___y_2973_;
v_a_2934_ = v_a_3006_;
goto v___jp_2926_;
}
}
else
{
lean_object* v_a_3007_; 
lean_dec(v___y_2970_);
lean_dec_ref(v_cfg_2905_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
v_a_3007_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_2994_);
v___y_2927_ = v___y_2967_;
v___y_2928_ = v___y_2968_;
v___y_2929_ = v___x_2993_;
v___y_2930_ = v___y_2971_;
v___y_2931_ = v_a_2975_;
v___y_2932_ = v___y_2972_;
v___y_2933_ = v___y_2973_;
v_a_2934_ = v_a_3007_;
goto v___jp_2926_;
}
}
}
v___jp_3008_:
{
if (v___y_3009_ == 0)
{
if (lean_obj_tag(v_goals_2899_) == 1)
{
lean_object* v_tail_3010_; 
v_tail_3010_ = lean_ctor_get(v_goals_2899_, 1);
lean_inc(v_tail_3010_);
if (lean_obj_tag(v_tail_3010_) == 0)
{
lean_object* v_toApplyRulesConfig_3011_; uint8_t v_exfalso_3012_; 
v_toApplyRulesConfig_3011_ = lean_ctor_get(v_cfg_2905_, 0);
lean_inc_ref(v_toApplyRulesConfig_3011_);
v_exfalso_3012_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3011_, sizeof(void*)*2 + 2);
lean_dec_ref(v_toApplyRulesConfig_3011_);
if (v_exfalso_3012_ == 1)
{
lean_object* v_options_3013_; uint8_t v_hasTrace_3014_; 
lean_dec_ref(v___x_2906_);
v_options_3013_ = lean_ctor_get(v_a_2902_, 2);
v_hasTrace_3014_ = lean_ctor_get_uint8(v_options_3013_, sizeof(void*)*1);
if (v_hasTrace_3014_ == 0)
{
lean_object* v_head_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3033_; 
v_head_3015_ = lean_ctor_get(v_goals_2899_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_goals_2899_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; 
v_unused_3034_ = lean_ctor_get(v_goals_2899_, 1);
lean_dec(v_unused_3034_);
v___x_3017_ = v_goals_2899_;
v_isShared_3018_ = v_isSharedCheck_3033_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_head_3015_);
lean_dec(v_goals_2899_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3033_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_MVarId_exfalso(v_head_3015_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3019_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v_a_3020_);
v___x_3022_ = v___x_3017_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3020_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_tail_3010_);
v___x_3022_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; 
v___x_3023_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2897_, v_ctx_2898_, v_cfg_2905_, v___x_3022_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
return v___x_3023_;
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_del_object(v___x_3017_);
lean_dec_ref(v_cfg_2905_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
v_a_3025_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3019_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3019_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
else
{
lean_object* v_head_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3062_; 
v_head_3035_ = lean_ctor_get(v_goals_2899_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_goals_2899_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v_goals_2899_, 1);
lean_dec(v_unused_3063_);
v___x_3037_ = v_goals_2899_;
v_isShared_3038_ = v_isSharedCheck_3062_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_head_3035_);
lean_dec(v_goals_2899_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3062_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3039_ = ((lean_object*)(l_Lean_Meta_SolveByElim_initFn___closed__3_00___x40_Lean_Meta_Tactic_SolveByElim_1979843508____hygCtx___hyg_2_));
v___x_3040_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_SolveByElim_applyTactics_spec__1___redArg(v___x_3039_, v_a_2902_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = ((lean_object*)(l_Lean_Meta_SolveByElim_applyTactics___redArg___lam__2___closed__0));
v___x_3043_ = lean_unbox(v_a_3041_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = l_Lean_trace_profiler;
v___x_3045_ = l_Lean_Option_get___at___00Lean_Meta_SolveByElim_applyTactics_spec__3(v_options_3013_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
lean_dec(v_a_3041_);
v___x_3046_ = l_Lean_MVarId_exfalso(v_head_3035_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v_a_3047_);
v___x_3049_ = v___x_3037_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_tail_3010_);
v___x_3049_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; 
v___x_3050_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_solveByElim_run(v_lemmas_2897_, v_ctx_2898_, v_cfg_2905_, v___x_3049_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
return v___x_3050_;
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_del_object(v___x_3037_);
lean_dec_ref(v_cfg_2905_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
v_a_3052_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3046_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3046_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
uint8_t v___x_3060_; 
lean_del_object(v___x_3037_);
v___x_3060_ = lean_unbox(v_a_3041_);
lean_dec(v_a_3041_);
v___y_2967_ = v___x_3039_;
v___y_2968_ = v_options_3013_;
v___y_2969_ = v_head_3035_;
v___y_2970_ = v_tail_3010_;
v___y_2971_ = v___x_3060_;
v___y_2972_ = v_exfalso_3012_;
v___y_2973_ = v___x_3042_;
goto v___jp_2966_;
}
}
else
{
uint8_t v___x_3061_; 
lean_del_object(v___x_3037_);
v___x_3061_ = lean_unbox(v_a_3041_);
lean_dec(v_a_3041_);
v___y_2967_ = v___x_3039_;
v___y_2968_ = v_options_3013_;
v___y_2969_ = v_head_3035_;
v___y_2970_ = v_tail_3010_;
v___y_2971_ = v___x_3061_;
v___y_2972_ = v_exfalso_3012_;
v___y_2973_ = v___x_3042_;
goto v___jp_2966_;
}
}
}
}
else
{
lean_dec_ref(v_goals_2899_);
lean_dec_ref(v_cfg_2905_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
return v___x_2906_;
}
}
else
{
lean_dec_ref(v_goals_2899_);
lean_dec(v_tail_3010_);
lean_dec_ref(v_cfg_2905_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
return v___x_2906_;
}
}
else
{
lean_dec_ref(v_cfg_2905_);
lean_dec(v_goals_2899_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
return v___x_2906_;
}
}
else
{
lean_dec_ref(v_cfg_2905_);
lean_dec(v_goals_2899_);
lean_dec_ref(v_ctx_2898_);
lean_dec(v_lemmas_2897_);
return v___x_2906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___boxed(lean_object* v_cfg_3066_, lean_object* v_lemmas_3067_, lean_object* v_ctx_3068_, lean_object* v_goals_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_3066_, v_lemmas_3067_, v_ctx_3068_, v_goals_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = l_List_reverse___redArg(v_x_3077_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
else
{
lean_object* v_head_3085_; lean_object* v_tail_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3109_; 
v_head_3085_ = lean_ctor_get(v_x_3076_, 0);
v_tail_3086_ = lean_ctor_get(v_x_3076_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_x_3076_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3088_ = v_x_3076_;
v_isShared_3089_ = v_isSharedCheck_3109_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_tail_3086_);
lean_inc(v_head_3085_);
lean_dec(v_x_3076_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3109_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Expr_applySymm(v_head_3085_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 1, v_x_3077_);
lean_ctor_set(v___x_3088_, 0, v_a_3091_);
v___x_3093_ = v___x_3088_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3091_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_x_3077_);
v___x_3093_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
v_x_3076_ = v_tail_3086_;
v_x_3077_ = v___x_3093_;
goto _start;
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3108_; 
lean_del_object(v___x_3088_);
v_a_3096_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3098_ = v___x_3090_;
v_isShared_3099_ = v_isSharedCheck_3108_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3090_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3108_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
uint8_t v___y_3101_; uint8_t v___x_3106_; 
v___x_3106_ = l_Lean_Exception_isInterrupt(v_a_3096_);
if (v___x_3106_ == 0)
{
uint8_t v___x_3107_; 
lean_inc(v_a_3096_);
v___x_3107_ = l_Lean_Exception_isRuntime(v_a_3096_);
v___y_3101_ = v___x_3107_;
goto v___jp_3100_;
}
else
{
v___y_3101_ = v___x_3106_;
goto v___jp_3100_;
}
v___jp_3100_:
{
if (v___y_3101_ == 0)
{
lean_del_object(v___x_3098_);
lean_dec(v_a_3096_);
v_x_3076_ = v_tail_3086_;
goto _start;
}
else
{
lean_object* v___x_3104_; 
lean_dec(v_tail_3086_);
lean_dec(v_x_3077_);
if (v_isShared_3099_ == 0)
{
v___x_3104_ = v___x_3098_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3096_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0___boxed(lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_x_3110_, v_x_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t v_symm_3118_, lean_object* v_hyps_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
if (v_symm_3118_ == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_hyps_3119_);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_box(0);
lean_inc(v_hyps_3119_);
v___x_3127_ = l_List_filterMapM_loop___at___00Lean_Meta_SolveByElim_saturateSymm_spec__0(v_hyps_3119_, v___x_3126_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = l_List_appendTR___redArg(v_hyps_3119_, v_a_3128_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_dec(v_hyps_3119_);
return v___x_3127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* v_symm_3137_, lean_object* v_hyps_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
uint8_t v_symm_boxed_3144_; lean_object* v_res_3145_; 
v_symm_boxed_3144_ = lean_unbox(v_symm_3137_);
v_res_3145_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_boxed_3144_, v_hyps_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_as_3146_, size_t v_sz_3147_, size_t v_i_3148_, lean_object* v_b_3149_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_lt(v_i_3148_, v_sz_3147_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_b_3149_);
return v___x_3152_;
}
else
{
lean_object* v_snd_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3171_; 
v_snd_3153_ = lean_ctor_get(v_b_3149_, 1);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_b_3149_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v_b_3149_, 0);
lean_dec(v_unused_3172_);
v___x_3155_ = v_b_3149_;
v_isShared_3156_ = v_isSharedCheck_3171_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_snd_3153_);
lean_dec(v_b_3149_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3171_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v_a_3159_; lean_object* v_a_3166_; 
v___x_3157_ = lean_box(0);
v_a_3166_ = lean_array_uget_borrowed(v_as_3146_, v_i_3148_);
if (lean_obj_tag(v_a_3166_) == 0)
{
v_a_3159_ = v_snd_3153_;
goto v___jp_3158_;
}
else
{
lean_object* v_val_3167_; uint8_t v___x_3168_; 
v_val_3167_ = lean_ctor_get(v_a_3166_, 0);
v___x_3168_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_inc(v_val_3167_);
v___x_3169_ = l_Lean_LocalDecl_toExpr(v_val_3167_);
v___x_3170_ = lean_array_push(v_snd_3153_, v___x_3169_);
v_a_3159_ = v___x_3170_;
goto v___jp_3158_;
}
else
{
v_a_3159_ = v_snd_3153_;
goto v___jp_3158_;
}
}
v___jp_3158_:
{
lean_object* v___x_3161_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v_a_3159_);
lean_ctor_set(v___x_3155_, 0, v___x_3157_);
v___x_3161_ = v___x_3155_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_a_3159_);
v___x_3161_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
size_t v___x_3162_; size_t v___x_3163_; 
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_add(v_i_3148_, v___x_3162_);
v_i_3148_ = v___x_3163_;
v_b_3149_ = v___x_3161_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_3173_, lean_object* v_sz_3174_, lean_object* v_i_3175_, lean_object* v_b_3176_, lean_object* v___y_3177_){
_start:
{
size_t v_sz_boxed_3178_; size_t v_i_boxed_3179_; lean_object* v_res_3180_; 
v_sz_boxed_3178_ = lean_unbox_usize(v_sz_3174_);
lean_dec(v_sz_3174_);
v_i_boxed_3179_ = lean_unbox_usize(v_i_3175_);
lean_dec(v_i_3175_);
v_res_3180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3173_, v_sz_boxed_3178_, v_i_boxed_3179_, v_b_3176_);
lean_dec_ref(v_as_3173_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(lean_object* v_as_3181_, size_t v_sz_3182_, size_t v_i_3183_, lean_object* v_b_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
uint8_t v___x_3192_; 
v___x_3192_ = lean_usize_dec_lt(v_i_3183_, v_sz_3182_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_b_3184_);
return v___x_3193_;
}
else
{
lean_object* v_snd_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3212_; 
v_snd_3194_ = lean_ctor_get(v_b_3184_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_b_3184_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_b_3184_, 0);
lean_dec(v_unused_3213_);
v___x_3196_ = v_b_3184_;
v_isShared_3197_ = v_isSharedCheck_3212_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_snd_3194_);
lean_dec(v_b_3184_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3212_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v_a_3200_; lean_object* v_a_3207_; 
v___x_3198_ = lean_box(0);
v_a_3207_ = lean_array_uget_borrowed(v_as_3181_, v_i_3183_);
if (lean_obj_tag(v_a_3207_) == 0)
{
v_a_3200_ = v_snd_3194_;
goto v___jp_3199_;
}
else
{
lean_object* v_val_3208_; uint8_t v___x_3209_; 
v_val_3208_ = lean_ctor_get(v_a_3207_, 0);
v___x_3209_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc(v_val_3208_);
v___x_3210_ = l_Lean_LocalDecl_toExpr(v_val_3208_);
v___x_3211_ = lean_array_push(v_snd_3194_, v___x_3210_);
v_a_3200_ = v___x_3211_;
goto v___jp_3199_;
}
else
{
v_a_3200_ = v_snd_3194_;
goto v___jp_3199_;
}
}
v___jp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 1, v_a_3200_);
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3202_ = v___x_3196_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_a_3200_);
v___x_3202_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
size_t v___x_3203_; size_t v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_add(v_i_3183_, v___x_3203_);
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3181_, v_sz_3182_, v___x_3204_, v___x_3202_);
return v___x_3205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3214_, lean_object* v_sz_3215_, lean_object* v_i_3216_, lean_object* v_b_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
size_t v_sz_boxed_3225_; size_t v_i_boxed_3226_; lean_object* v_res_3227_; 
v_sz_boxed_3225_ = lean_unbox_usize(v_sz_3215_);
lean_dec(v_sz_3215_);
v_i_boxed_3226_ = lean_unbox_usize(v_i_3216_);
lean_dec(v_i_3216_);
v_res_3227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_as_3214_, v_sz_boxed_3225_, v_i_boxed_3226_, v_b_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec_ref(v_as_3214_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_as_3228_, size_t v_sz_3229_, size_t v_i_3230_, lean_object* v_b_3231_){
_start:
{
uint8_t v___x_3233_; 
v___x_3233_ = lean_usize_dec_lt(v_i_3230_, v_sz_3229_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_b_3231_);
return v___x_3234_;
}
else
{
lean_object* v_snd_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3253_; 
v_snd_3235_ = lean_ctor_get(v_b_3231_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_b_3231_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v_b_3231_, 0);
lean_dec(v_unused_3254_);
v___x_3237_ = v_b_3231_;
v_isShared_3238_ = v_isSharedCheck_3253_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_snd_3235_);
lean_dec(v_b_3231_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3253_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v_a_3241_; lean_object* v_a_3248_; 
v___x_3239_ = lean_box(0);
v_a_3248_ = lean_array_uget_borrowed(v_as_3228_, v_i_3230_);
if (lean_obj_tag(v_a_3248_) == 0)
{
v_a_3241_ = v_snd_3235_;
goto v___jp_3240_;
}
else
{
lean_object* v_val_3249_; uint8_t v___x_3250_; 
v_val_3249_ = lean_ctor_get(v_a_3248_, 0);
v___x_3250_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_inc(v_val_3249_);
v___x_3251_ = l_Lean_LocalDecl_toExpr(v_val_3249_);
v___x_3252_ = lean_array_push(v_snd_3235_, v___x_3251_);
v_a_3241_ = v___x_3252_;
goto v___jp_3240_;
}
else
{
v_a_3241_ = v_snd_3235_;
goto v___jp_3240_;
}
}
v___jp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 1, v_a_3241_);
lean_ctor_set(v___x_3237_, 0, v___x_3239_);
v___x_3243_ = v___x_3237_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_a_3241_);
v___x_3243_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
size_t v___x_3244_; size_t v___x_3245_; 
v___x_3244_ = ((size_t)1ULL);
v___x_3245_ = lean_usize_add(v_i_3230_, v___x_3244_);
v_i_3230_ = v___x_3245_;
v_b_3231_ = v___x_3243_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_as_3255_, lean_object* v_sz_3256_, lean_object* v_i_3257_, lean_object* v_b_3258_, lean_object* v___y_3259_){
_start:
{
size_t v_sz_boxed_3260_; size_t v_i_boxed_3261_; lean_object* v_res_3262_; 
v_sz_boxed_3260_ = lean_unbox_usize(v_sz_3256_);
lean_dec(v_sz_3256_);
v_i_boxed_3261_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_res_3262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3255_, v_sz_boxed_3260_, v_i_boxed_3261_, v_b_3258_);
lean_dec_ref(v_as_3255_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_3263_, size_t v_sz_3264_, size_t v_i_3265_, lean_object* v_b_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v___x_3274_; 
v___x_3274_ = lean_usize_dec_lt(v_i_3265_, v_sz_3264_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_b_3266_);
return v___x_3275_;
}
else
{
lean_object* v_snd_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3294_; 
v_snd_3276_ = lean_ctor_get(v_b_3266_, 1);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_b_3266_);
if (v_isSharedCheck_3294_ == 0)
{
lean_object* v_unused_3295_; 
v_unused_3295_ = lean_ctor_get(v_b_3266_, 0);
lean_dec(v_unused_3295_);
v___x_3278_ = v_b_3266_;
v_isShared_3279_ = v_isSharedCheck_3294_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snd_3276_);
lean_dec(v_b_3266_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3294_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v_a_3282_; lean_object* v_a_3289_; 
v___x_3280_ = lean_box(0);
v_a_3289_ = lean_array_uget_borrowed(v_as_3263_, v_i_3265_);
if (lean_obj_tag(v_a_3289_) == 0)
{
v_a_3282_ = v_snd_3276_;
goto v___jp_3281_;
}
else
{
lean_object* v_val_3290_; uint8_t v___x_3291_; 
v_val_3290_ = lean_ctor_get(v_a_3289_, 0);
v___x_3291_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc(v_val_3290_);
v___x_3292_ = l_Lean_LocalDecl_toExpr(v_val_3290_);
v___x_3293_ = lean_array_push(v_snd_3276_, v___x_3292_);
v_a_3282_ = v___x_3293_;
goto v___jp_3281_;
}
else
{
v_a_3282_ = v_snd_3276_;
goto v___jp_3281_;
}
}
v___jp_3281_:
{
lean_object* v___x_3284_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 1, v_a_3282_);
lean_ctor_set(v___x_3278_, 0, v___x_3280_);
v___x_3284_ = v___x_3278_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_a_3282_);
v___x_3284_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
size_t v___x_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = ((size_t)1ULL);
v___x_3286_ = lean_usize_add(v_i_3265_, v___x_3285_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3263_, v_sz_3264_, v___x_3286_, v___x_3284_);
return v___x_3287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_3296_, lean_object* v_sz_3297_, lean_object* v_i_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
size_t v_sz_boxed_3307_; size_t v_i_boxed_3308_; lean_object* v_res_3309_; 
v_sz_boxed_3307_ = lean_unbox_usize(v_sz_3297_);
lean_dec(v_sz_3297_);
v_i_boxed_3308_ = lean_unbox_usize(v_i_3298_);
lean_dec(v_i_3298_);
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_as_3296_, v_sz_boxed_3307_, v_i_boxed_3308_, v_b_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec_ref(v_as_3296_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(lean_object* v_inh_3310_, lean_object* v_n_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
if (lean_obj_tag(v_n_3311_) == 0)
{
lean_object* v_cs_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3354_; 
v_cs_3320_ = lean_ctor_get(v_n_3311_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_n_3311_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3322_ = v_n_3311_;
v_isShared_3323_ = v_isSharedCheck_3354_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_cs_3320_);
lean_dec(v_n_3311_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3354_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; size_t v_sz_3326_; size_t v___x_3327_; lean_object* v___x_3328_; 
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v_b_3312_);
v_sz_3326_ = lean_array_size(v_cs_3320_);
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_inh_3310_, v_cs_3320_, v_sz_3326_, v___x_3327_, v___x_3325_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec_ref(v_cs_3320_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3345_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3345_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3345_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_fst_3333_; 
v_fst_3333_ = lean_ctor_get(v_a_3329_, 0);
if (lean_obj_tag(v_fst_3333_) == 0)
{
lean_object* v_snd_3334_; lean_object* v___x_3336_; 
v_snd_3334_ = lean_ctor_get(v_a_3329_, 1);
lean_inc(v_snd_3334_);
lean_dec(v_a_3329_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set_tag(v___x_3322_, 1);
lean_ctor_set(v___x_3322_, 0, v_snd_3334_);
v___x_3336_ = v___x_3322_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_snd_3334_);
v___x_3336_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3336_);
v___x_3338_ = v___x_3331_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_object* v_val_3341_; lean_object* v___x_3343_; 
lean_inc_ref(v_fst_3333_);
lean_dec(v_a_3329_);
lean_del_object(v___x_3322_);
v_val_3341_ = lean_ctor_get(v_fst_3333_, 0);
lean_inc(v_val_3341_);
lean_dec_ref(v_fst_3333_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v_val_3341_);
v___x_3343_ = v___x_3331_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_val_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_del_object(v___x_3322_);
v_a_3346_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3328_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3328_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
else
{
lean_object* v_vs_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3389_; 
v_vs_3355_ = lean_ctor_get(v_n_3311_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_n_3311_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3357_ = v_n_3311_;
v_isShared_3358_ = v_isSharedCheck_3389_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_vs_3355_);
lean_dec(v_n_3311_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3389_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; size_t v_sz_3361_; size_t v___x_3362_; lean_object* v___x_3363_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
lean_ctor_set(v___x_3360_, 1, v_b_3312_);
v_sz_3361_ = lean_array_size(v_vs_3355_);
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3(v_vs_3355_, v_sz_3361_, v___x_3362_, v___x_3360_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec_ref(v_vs_3355_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3380_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3380_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3380_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; 
v_fst_3368_ = lean_ctor_get(v_a_3364_, 0);
if (lean_obj_tag(v_fst_3368_) == 0)
{
lean_object* v_snd_3369_; lean_object* v___x_3371_; 
v_snd_3369_ = lean_ctor_get(v_a_3364_, 1);
lean_inc(v_snd_3369_);
lean_dec(v_a_3364_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v_snd_3369_);
v___x_3371_ = v___x_3357_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_snd_3369_);
v___x_3371_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3371_);
v___x_3373_ = v___x_3366_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3378_; 
lean_inc_ref(v_fst_3368_);
lean_dec(v_a_3364_);
lean_del_object(v___x_3357_);
v_val_3376_ = lean_ctor_get(v_fst_3368_, 0);
lean_inc(v_val_3376_);
lean_dec_ref(v_fst_3368_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_val_3376_);
v___x_3378_ = v___x_3366_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_val_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_del_object(v___x_3357_);
v_a_3381_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3363_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3363_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(lean_object* v_inh_3390_, lean_object* v_as_3391_, size_t v_sz_3392_, size_t v_i_3393_, lean_object* v_b_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_usize_dec_lt(v_i_3393_, v_sz_3392_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_b_3394_);
return v___x_3403_;
}
else
{
lean_object* v_snd_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3438_; 
v_snd_3404_ = lean_ctor_get(v_b_3394_, 1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_b_3394_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v_b_3394_, 0);
lean_dec(v_unused_3439_);
v___x_3406_ = v_b_3394_;
v_isShared_3407_ = v_isSharedCheck_3438_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_snd_3404_);
lean_dec(v_b_3394_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3438_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_array_uget_borrowed(v_as_3391_, v_i_3393_);
lean_inc(v_snd_3404_);
lean_inc(v_a_3408_);
v___x_3409_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_inh_3390_, v_a_3408_, v_snd_3404_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3429_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3412_ = v___x_3409_;
v_isShared_3413_ = v_isSharedCheck_3429_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3429_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
if (lean_obj_tag(v_a_3410_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3414_, 0, v_a_3410_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3414_);
v___x_3416_ = v___x_3406_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_snd_3404_);
v___x_3416_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3418_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3416_);
v___x_3418_ = v___x_3412_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_del_object(v___x_3412_);
lean_dec(v_snd_3404_);
v_a_3421_ = lean_ctor_get(v_a_3410_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v_a_3410_);
v___x_3422_ = lean_box(0);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v_a_3421_);
lean_ctor_set(v___x_3406_, 0, v___x_3422_);
v___x_3424_ = v___x_3406_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_a_3421_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
size_t v___x_3425_; size_t v___x_3426_; 
v___x_3425_ = ((size_t)1ULL);
v___x_3426_ = lean_usize_add(v_i_3393_, v___x_3425_);
v_i_3393_ = v___x_3426_;
v_b_3394_ = v___x_3424_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_del_object(v___x_3406_);
lean_dec(v_snd_3404_);
v_a_3430_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3409_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3409_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_inh_3440_, lean_object* v_as_3441_, lean_object* v_sz_3442_, lean_object* v_i_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
size_t v_sz_boxed_3452_; size_t v_i_boxed_3453_; lean_object* v_res_3454_; 
v_sz_boxed_3452_ = lean_unbox_usize(v_sz_3442_);
lean_dec(v_sz_3442_);
v_i_boxed_3453_ = lean_unbox_usize(v_i_3443_);
lean_dec(v_i_3443_);
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__2(v_inh_3440_, v_as_3441_, v_sz_boxed_3452_, v_i_boxed_3453_, v_b_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v_as_3441_);
lean_dec_ref(v_inh_3440_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_3455_, lean_object* v_n_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_inh_3455_, v_n_3456_, v_b_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v_inh_3455_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(lean_object* v_t_3466_, lean_object* v_init_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_root_3475_; lean_object* v_tail_3476_; lean_object* v___x_3477_; 
v_root_3475_ = lean_ctor_get(v_t_3466_, 0);
lean_inc_ref(v_root_3475_);
v_tail_3476_ = lean_ctor_get(v_t_3466_, 1);
lean_inc_ref(v_tail_3476_);
lean_dec_ref(v_t_3466_);
lean_inc_ref(v_init_3467_);
v___x_3477_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1(v_init_3467_, v_root_3475_, v_init_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec_ref(v_init_3467_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3514_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3514_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3514_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
if (lean_obj_tag(v_a_3478_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; 
lean_dec_ref(v_tail_3476_);
v_a_3482_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v_a_3478_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v_a_3482_);
v___x_3484_ = v___x_3480_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; size_t v_sz_3489_; size_t v___x_3490_; lean_object* v___x_3491_; 
lean_del_object(v___x_3480_);
v_a_3486_ = lean_ctor_get(v_a_3478_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v_a_3478_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v_a_3486_);
v_sz_3489_ = lean_array_size(v_tail_3476_);
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2(v_tail_3476_, v_sz_3489_, v___x_3490_, v___x_3488_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec_ref(v_tail_3476_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3505_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3505_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3505_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v_fst_3496_; 
v_fst_3496_ = lean_ctor_get(v_a_3492_, 0);
if (lean_obj_tag(v_fst_3496_) == 0)
{
lean_object* v_snd_3497_; lean_object* v___x_3499_; 
v_snd_3497_ = lean_ctor_get(v_a_3492_, 1);
lean_inc(v_snd_3497_);
lean_dec(v_a_3492_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_snd_3497_);
v___x_3499_ = v___x_3494_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_snd_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
else
{
lean_object* v_val_3501_; lean_object* v___x_3503_; 
lean_inc_ref(v_fst_3496_);
lean_dec(v_a_3492_);
v_val_3501_ = lean_ctor_get(v_fst_3496_, 0);
lean_inc(v_val_3501_);
lean_dec_ref(v_fst_3496_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_val_3501_);
v___x_3503_ = v___x_3494_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_val_3501_);
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
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
v_a_3506_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3491_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3491_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec_ref(v_tail_3476_);
v_a_3515_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3477_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3477_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0___boxed(lean_object* v_t_3523_, lean_object* v_init_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_t_3523_, v_init_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_lctx_3542_; lean_object* v_decls_3543_; lean_object* v_hs_3544_; lean_object* v___x_3545_; 
v_lctx_3542_ = lean_ctor_get(v___y_3537_, 2);
v_decls_3543_ = lean_ctor_get(v_lctx_3542_, 1);
lean_inc_ref(v_decls_3543_);
v_hs_3544_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___closed__0));
v___x_3545_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0(v_decls_3543_, v_hs_3544_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec_ref(v___y_3537_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0___boxed(lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0(uint8_t v_only_3554_, lean_object* v_cfg_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
if (v_only_3554_ == 0)
{
lean_object* v___x_3563_; 
lean_inc_ref(v___y_3558_);
v___x_3563_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_toApplyRulesConfig_3564_; lean_object* v_a_3565_; uint8_t v_symm_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_toApplyRulesConfig_3564_ = lean_ctor_get(v_cfg_3555_, 0);
v_a_3565_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3565_);
lean_dec_ref(v___x_3563_);
v_symm_3566_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3564_, sizeof(void*)*2 + 1);
v___x_3567_ = lean_array_to_list(v_a_3565_);
v___x_3568_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3566_, v___x_3567_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
return v___x_3568_;
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
v_a_3569_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3563_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3563_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lam__0___boxed(lean_object* v_only_3579_, lean_object* v_cfg_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
uint8_t v_only_boxed_3588_; lean_object* v_res_3589_; 
v_only_boxed_3588_ = lean_unbox(v_only_3579_);
v_res_3589_ = l_Lean_MVarId_applyRules___lam__0(v_only_boxed_3588_, v_cfg_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v_cfg_3580_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* v_cfg_3590_, lean_object* v_lemmas_3591_, uint8_t v_only_3592_, lean_object* v_g_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_toApplyRulesConfig_3599_; uint8_t v_intro_3600_; uint8_t v_constructor_3601_; uint8_t v_suggestions_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3615_; 
v_toApplyRulesConfig_3599_ = lean_ctor_get(v_cfg_3590_, 0);
v_intro_3600_ = lean_ctor_get_uint8(v_cfg_3590_, sizeof(void*)*1 + 1);
v_constructor_3601_ = lean_ctor_get_uint8(v_cfg_3590_, sizeof(void*)*1 + 2);
v_suggestions_3602_ = lean_ctor_get_uint8(v_cfg_3590_, sizeof(void*)*1 + 3);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_cfg_3590_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3604_ = v_cfg_3590_;
v_isShared_3605_ = v_isSharedCheck_3615_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_toApplyRulesConfig_3599_);
lean_dec(v_cfg_3590_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3615_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v_ctx_3607_; uint8_t v___x_3608_; lean_object* v___x_3610_; 
v___x_3606_ = lean_box(v_only_3592_);
v_ctx_3607_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lam__0___boxed), 9, 1);
lean_closure_set(v_ctx_3607_, 0, v___x_3606_);
v___x_3608_ = 0;
if (v_isShared_3605_ == 0)
{
v___x_3610_ = v___x_3604_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_toApplyRulesConfig_3599_);
lean_ctor_set_uint8(v_reuseFailAlloc_3614_, sizeof(void*)*1 + 1, v_intro_3600_);
lean_ctor_set_uint8(v_reuseFailAlloc_3614_, sizeof(void*)*1 + 2, v_constructor_3601_);
lean_ctor_set_uint8(v_reuseFailAlloc_3614_, sizeof(void*)*1 + 3, v_suggestions_3602_);
v___x_3610_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*1, v___x_3608_);
v___x_3611_ = lean_box(0);
v___x_3612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_g_3593_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_3610_, v_lemmas_3591_, v_ctx_3607_, v___x_3612_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* v_cfg_3616_, lean_object* v_lemmas_3617_, lean_object* v_only_3618_, lean_object* v_g_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
uint8_t v_only_boxed_3625_; lean_object* v_res_3626_; 
v_only_boxed_3625_ = lean_unbox(v_only_3618_);
v_res_3626_ = l_Lean_MVarId_applyRules(v_cfg_3616_, v_lemmas_3617_, v_only_boxed_3625_, v_g_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_3627_, size_t v_sz_3628_, size_t v_i_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___redArg(v_as_3627_, v_sz_3628_, v_i_3629_, v_b_3630_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_3639_, lean_object* v_sz_3640_, lean_object* v_i_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
size_t v_sz_boxed_3650_; size_t v_i_boxed_3651_; lean_object* v_res_3652_; 
v_sz_boxed_3650_ = lean_unbox_usize(v_sz_3640_);
lean_dec(v_sz_3640_);
v_i_boxed_3651_ = lean_unbox_usize(v_i_3641_);
lean_dec(v_i_3641_);
v_res_3652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__2_spec__5(v_as_3639_, v_sz_boxed_3650_, v_i_boxed_3651_, v_b_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec_ref(v_as_3639_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_as_3653_, size_t v_sz_3654_, size_t v_i_3655_, lean_object* v_b_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_as_3653_, v_sz_3654_, v_i_3655_, v_b_3656_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_as_3665_, lean_object* v_sz_3666_, lean_object* v_i_3667_, lean_object* v_b_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
size_t v_sz_boxed_3676_; size_t v_i_boxed_3677_; lean_object* v_res_3678_; 
v_sz_boxed_3676_ = lean_unbox_usize(v_sz_3666_);
lean_dec(v_sz_3666_);
v_i_boxed_3677_ = lean_unbox_usize(v_i_3667_);
lean_dec(v_i_3667_);
v_res_3678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0_spec__0_spec__1_spec__3_spec__4(v_as_3665_, v_sz_boxed_3676_, v_i_boxed_3677_, v_b_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec_ref(v_as_3665_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* v_t_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; 
v___x_3687_ = lean_box(0);
v___x_3688_ = 1;
v___x_3689_ = l_Lean_Elab_Term_elabTerm(v_t_3679_, v___x_3687_, v___x_3688_, v___x_3688_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed(lean_object* v_t_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_t_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v_ref_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_ref_3704_ = lean_ctor_get(v___y_3701_, 5);
v___x_3705_ = 0;
v___x_3706_ = l_Lean_SourceInfo_fromRef(v_ref_3704_, v___x_3705_);
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0___boxed(lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
return v_res_3713_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(lean_object* v_a_3714_, lean_object* v_x_3715_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
uint8_t v___x_3716_; 
v___x_3716_ = 0;
return v___x_3716_;
}
else
{
lean_object* v_head_3717_; lean_object* v_tail_3718_; uint8_t v___x_3719_; 
v_head_3717_ = lean_ctor_get(v_x_3715_, 0);
v_tail_3718_ = lean_ctor_get(v_x_3715_, 1);
v___x_3719_ = lean_expr_eqv(v_a_3714_, v_head_3717_);
if (v___x_3719_ == 0)
{
v_x_3715_ = v_tail_3718_;
goto _start;
}
else
{
return v___x_3719_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2___boxed(lean_object* v_a_3721_, lean_object* v_x_3722_){
_start:
{
uint8_t v_res_3723_; lean_object* v_r_3724_; 
v_res_3723_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_a_3721_, v_x_3722_);
lean_dec(v_x_3722_);
lean_dec_ref(v_a_3721_);
v_r_3724_ = lean_box(v_res_3723_);
return v_r_3724_;
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(lean_object* v_ys_3725_, lean_object* v_x_3726_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = l_List_elem___at___00List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2_spec__2(v_x_3726_, v_ys_3725_);
if (v___x_3727_ == 0)
{
uint8_t v___x_3728_; 
v___x_3728_ = 1;
return v___x_3728_;
}
else
{
uint8_t v___x_3729_; 
v___x_3729_ = 0;
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed(lean_object* v_ys_3730_, lean_object* v_x_3731_){
_start:
{
uint8_t v_res_3732_; lean_object* v_r_3733_; 
v_res_3732_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0(v_ys_3730_, v_x_3731_);
lean_dec_ref(v_x_3731_);
lean_dec(v_ys_3730_);
v_r_3733_ = lean_box(v_res_3732_);
return v_r_3733_;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(lean_object* v_xs_3734_, lean_object* v_ys_3735_){
_start:
{
lean_object* v___f_3736_; lean_object* v___x_3737_; 
v___f_3736_ = lean_alloc_closure((void*)(l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3736_, 0, v_ys_3735_);
v___x_3737_ = l_List_filter___redArg(v___f_3736_, v_xs_3734_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(lean_object* v_x_3738_, lean_object* v_x_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
if (lean_obj_tag(v_x_3738_) == 0)
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = l_List_reverse___redArg(v_x_3739_);
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
return v___x_3748_;
}
else
{
lean_object* v_head_3749_; lean_object* v_tail_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3768_; 
v_head_3749_ = lean_ctor_get(v_x_3738_, 0);
v_tail_3750_ = lean_ctor_get(v_x_3738_, 1);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_x_3738_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3752_ = v_x_3738_;
v_isShared_3753_ = v_isSharedCheck_3768_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_tail_3750_);
lean_inc(v_head_3749_);
lean_dec(v_x_3738_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3768_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; 
v___x_3754_ = l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(v_head_3749_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref(v___x_3754_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 1, v_x_3739_);
lean_ctor_set(v___x_3752_, 0, v_a_3755_);
v___x_3757_ = v___x_3752_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3755_);
lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_x_3739_);
v___x_3757_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
v_x_3738_ = v_tail_3750_;
v_x_3739_ = v___x_3757_;
goto _start;
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_del_object(v___x_3752_);
lean_dec(v_tail_3750_);
lean_dec(v_x_3739_);
v_a_3760_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3754_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3754_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1___boxed(lean_object* v_x_3769_, lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_x_3769_, v_x_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(lean_object* v_remove_3779_, uint8_t v_noDefaults_3780_, uint8_t v_star_3781_, lean_object* v_cfg_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
if (v_noDefaults_3780_ == 0)
{
goto v___jp_3790_;
}
else
{
if (v_star_3781_ == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
lean_dec(v_remove_3779_);
v___x_3809_ = lean_box(0);
v___x_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
return v___x_3810_;
}
else
{
goto v___jp_3790_;
}
}
v___jp_3790_:
{
lean_object* v___x_3791_; 
lean_inc_ref(v___y_3785_);
v___x_3791_ = l_Lean_getLocalHyps___at___00Lean_MVarId_applyRules_spec__0(v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = lean_box(0);
v___x_3794_ = l_List_mapM_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__1(v_remove_3779_, v___x_3793_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_toApplyRulesConfig_3795_; lean_object* v_a_3796_; uint8_t v_symm_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_toApplyRulesConfig_3795_ = lean_ctor_get(v_cfg_3782_, 0);
v_a_3796_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3794_);
v_symm_3797_ = lean_ctor_get_uint8(v_toApplyRulesConfig_3795_, sizeof(void*)*2 + 1);
v___x_3798_ = lean_array_to_list(v_a_3792_);
v___x_3799_ = l_List_removeAll___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__2(v___x_3798_, v_a_3796_);
v___x_3800_ = l_Lean_Meta_SolveByElim_saturateSymm(v_symm_3797_, v___x_3799_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3800_;
}
else
{
lean_dec(v_a_3792_);
return v___x_3794_;
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v_remove_3779_);
v_a_3801_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3791_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3791_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed(lean_object* v_remove_3811_, lean_object* v_noDefaults_3812_, lean_object* v_star_3813_, lean_object* v_cfg_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v_noDefaults_boxed_3822_; uint8_t v_star_boxed_3823_; lean_object* v_res_3824_; 
v_noDefaults_boxed_3822_ = lean_unbox(v_noDefaults_3812_);
v_star_boxed_3823_ = lean_unbox(v_star_3813_);
v_res_3824_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1(v_remove_3811_, v_noDefaults_boxed_3822_, v_star_boxed_3823_, v_cfg_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v_cfg_3814_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(lean_object* v_as_3825_, size_t v_i_3826_, size_t v_stop_3827_, lean_object* v_b_3828_){
_start:
{
uint8_t v___x_3829_; 
v___x_3829_ = lean_usize_dec_eq(v_i_3826_, v_stop_3827_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; size_t v___x_3832_; size_t v___x_3833_; 
v___x_3830_ = lean_array_uget_borrowed(v_as_3825_, v_i_3826_);
v___x_3831_ = l_Array_append___redArg(v_b_3828_, v___x_3830_);
v___x_3832_ = ((size_t)1ULL);
v___x_3833_ = lean_usize_add(v_i_3826_, v___x_3832_);
v_i_3826_ = v___x_3833_;
v_b_3828_ = v___x_3831_;
goto _start;
}
else
{
return v_b_3828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5___boxed(lean_object* v_as_3835_, lean_object* v_i_3836_, lean_object* v_stop_3837_, lean_object* v_b_3838_){
_start:
{
size_t v_i_boxed_3839_; size_t v_stop_boxed_3840_; lean_object* v_res_3841_; 
v_i_boxed_3839_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_stop_boxed_3840_ = lean_unbox_usize(v_stop_3837_);
lean_dec(v_stop_3837_);
v_res_3841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_as_3835_, v_i_boxed_3839_, v_stop_boxed_3840_, v_b_3838_);
lean_dec_ref(v_as_3835_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
if (lean_obj_tag(v_a_3842_) == 0)
{
lean_object* v___x_3844_; 
v___x_3844_ = l_List_reverse___redArg(v_a_3843_);
return v___x_3844_;
}
else
{
lean_object* v_head_3845_; lean_object* v_tail_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3855_; 
v_head_3845_ = lean_ctor_get(v_a_3842_, 0);
v_tail_3846_ = lean_ctor_get(v_a_3842_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_a_3842_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3848_ = v_a_3842_;
v_isShared_3849_ = v_isSharedCheck_3855_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_tail_3846_);
lean_inc(v_head_3845_);
lean_dec(v_a_3842_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3855_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_SolveByElim_0__Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27___boxed), 8, 1);
lean_closure_set(v___x_3850_, 0, v_head_3845_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 1, v_a_3843_);
lean_ctor_set(v___x_3848_, 0, v___x_3850_);
v___x_3852_ = v___x_3848_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_a_3843_);
v___x_3852_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
v_a_3842_ = v_tail_3846_;
v_a_3843_ = v___x_3852_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(size_t v_sz_3856_, size_t v_i_3857_, lean_object* v_bs_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_usize_dec_lt(v_i_3857_, v_sz_3856_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_bs_3858_);
return v___x_3863_;
}
else
{
lean_object* v_v_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_v_3864_ = lean_array_uget_borrowed(v_bs_3858_, v_i_3857_);
v___x_3865_ = l_Lean_Syntax_getId(v_v_3864_);
v___x_3866_ = l_Lean_labelled(v___x_3865_, v___y_3859_, v___y_3860_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3868_; lean_object* v_bs_x27_3869_; size_t v___x_3870_; size_t v___x_3871_; lean_object* v___x_3872_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = lean_unsigned_to_nat(0u);
v_bs_x27_3869_ = lean_array_uset(v_bs_3858_, v_i_3857_, v___x_3868_);
v___x_3870_ = ((size_t)1ULL);
v___x_3871_ = lean_usize_add(v_i_3857_, v___x_3870_);
v___x_3872_ = lean_array_uset(v_bs_x27_3869_, v_i_3857_, v_a_3867_);
v_i_3857_ = v___x_3871_;
v_bs_3858_ = v___x_3872_;
goto _start;
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_bs_3858_);
v_a_3874_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3866_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3866_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg___boxed(lean_object* v_sz_3882_, lean_object* v_i_3883_, lean_object* v_bs_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
size_t v_sz_boxed_3888_; size_t v_i_boxed_3889_; lean_object* v_res_3890_; 
v_sz_boxed_3888_ = lean_unbox_usize(v_sz_3882_);
lean_dec(v_sz_3882_);
v_i_boxed_3889_ = lean_unbox_usize(v_i_3883_);
lean_dec(v_i_3883_);
v_res_3890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_boxed_3888_, v_i_boxed_3889_, v_bs_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(lean_object* v_head_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_head_3891_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed(lean_object* v_head_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0(v_head_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
if (lean_obj_tag(v_a_3909_) == 0)
{
lean_object* v___x_3911_; 
v___x_3911_ = l_List_reverse___redArg(v_a_3910_);
return v___x_3911_;
}
else
{
lean_object* v_head_3912_; lean_object* v_tail_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3922_; 
v_head_3912_ = lean_ctor_get(v_a_3909_, 0);
v_tail_3913_ = lean_ctor_get(v_a_3909_, 1);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_a_3909_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3915_ = v_a_3909_;
v_isShared_3916_ = v_isSharedCheck_3922_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_tail_3913_);
lean_inc(v_head_3912_);
lean_dec(v_a_3909_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3922_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___f_3917_; lean_object* v___x_3919_; 
v___f_3917_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3917_, 0, v_head_3912_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 1, v_a_3910_);
lean_ctor_set(v___x_3915_, 0, v___f_3917_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___f_3917_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_a_3910_);
v___x_3919_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
v_a_3909_ = v_tail_3913_;
v_a_3910_ = v___x_3919_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__0));
v___x_3925_ = l_Lean_stringToMessageData(v___x_3924_);
return v___x_3925_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2));
v___x_3928_ = l_String_toRawSubstring_x27(v___x_3927_);
return v___x_3928_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__5));
v___x_3933_ = l_String_toRawSubstring_x27(v___x_3932_);
return v___x_3933_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__8));
v___x_3938_ = l_String_toRawSubstring_x27(v___x_3937_);
return v___x_3938_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__11));
v___x_3943_ = l_String_toRawSubstring_x27(v___x_3942_);
return v___x_3943_;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__23));
v___x_3974_ = l_Lean_stringToMessageData(v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t v_noDefaults_3975_, uint8_t v_star_3976_, lean_object* v_add_3977_, lean_object* v_remove_3978_, lean_object* v_use_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___f_4010_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; 
v___x_4008_ = lean_box(v_noDefaults_3975_);
v___x_4009_ = lean_box(v_star_3976_);
lean_inc(v_remove_3978_);
v___f_4010_ = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__1___boxed), 11, 3);
lean_closure_set(v___f_4010_, 0, v_remove_3978_);
lean_closure_set(v___f_4010_, 1, v___x_4008_);
lean_closure_set(v___f_4010_, 2, v___x_4009_);
if (v_star_3976_ == 0)
{
lean_inc_ref(v_a_3982_);
v___y_4027_ = v_a_3980_;
v___y_4028_ = v_a_3981_;
v___y_4029_ = v_a_3982_;
v___y_4030_ = v_a_3983_;
goto v___jp_4026_;
}
else
{
if (v_noDefaults_3975_ == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v___f_4010_);
lean_dec_ref(v_use_3979_);
lean_dec(v_remove_3978_);
lean_dec(v_add_3977_);
v___x_4089_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__24);
v___x_4090_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_4089_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
else
{
lean_inc_ref(v_a_3982_);
v___y_4027_ = v_a_3980_;
v___y_4028_ = v_a_3981_;
v___y_4029_ = v_a_3982_;
v___y_4030_ = v_a_3983_;
goto v___jp_4026_;
}
}
v___jp_3985_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___y_3986_);
lean_ctor_set(v___x_3988_, 1, v___y_3987_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
v___jp_3990_:
{
uint8_t v___x_3997_; 
v___x_3997_ = l_List_isEmpty___redArg(v_remove_3978_);
lean_dec(v_remove_3978_);
if (v___x_3997_ == 0)
{
if (v_noDefaults_3975_ == 0)
{
lean_dec_ref(v___y_3991_);
v___y_3986_ = v___y_3996_;
v___y_3987_ = v___y_3995_;
goto v___jp_3985_;
}
else
{
if (v_star_3976_ == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
v___x_3998_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
v___x_3999_ = l_Lean_throwError___at___00Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions_spec__3___redArg(v___x_3998_, v___y_3994_, v___y_3993_, v___y_3991_, v___y_3992_);
lean_dec_ref(v___y_3991_);
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
else
{
lean_dec_ref(v___y_3991_);
v___y_3986_ = v___y_3996_;
v___y_3987_ = v___y_3995_;
goto v___jp_3985_;
}
}
}
else
{
lean_dec_ref(v___y_3991_);
v___y_3986_ = v___y_3996_;
v___y_3987_ = v___y_3995_;
goto v___jp_3985_;
}
}
v___jp_4011_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_array_to_list(v___y_4018_);
lean_inc(v___y_4014_);
v___x_4020_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__4(v___x_4019_, v___y_4014_);
if (v_noDefaults_3975_ == 0)
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4021_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3977_, v___y_4014_);
v___x_4022_ = l_List_appendTR___redArg(v___x_4021_, v___x_4020_);
v___x_4023_ = l_List_appendTR___redArg(v___x_4022_, v___y_4017_);
v___y_3991_ = v___y_4012_;
v___y_3992_ = v___y_4013_;
v___y_3993_ = v___y_4016_;
v___y_3994_ = v___y_4015_;
v___y_3995_ = v___f_4010_;
v___y_3996_ = v___x_4023_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_dec(v___y_4017_);
v___x_4024_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v_add_3977_, v___y_4014_);
v___x_4025_ = l_List_appendTR___redArg(v___x_4024_, v___x_4020_);
v___y_3991_ = v___y_4012_;
v___y_3992_ = v___y_4013_;
v___y_3993_ = v___y_4016_;
v___y_3994_ = v___y_4015_;
v___y_3995_ = v___f_4010_;
v___y_3996_ = v___x_4025_;
goto v___jp_3990_;
}
}
v___jp_4026_:
{
lean_object* v_ref_4031_; lean_object* v_quotContext_4032_; lean_object* v_currMacroScope_4033_; lean_object* v___x_4034_; lean_object* v_a_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v_a_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v_a_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; size_t v_sz_4047_; size_t v___x_4048_; lean_object* v___x_4049_; 
v_ref_4031_ = lean_ctor_get(v___y_4029_, 5);
v_quotContext_4032_ = lean_ctor_get(v___y_4029_, 10);
v_currMacroScope_4033_ = lean_ctor_get(v___y_4029_, 11);
v___x_4034_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref(v___x_4034_);
v___x_4036_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__3);
v___x_4037_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref(v___x_4037_);
v___x_4039_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__4));
lean_inc(v_currMacroScope_4033_);
lean_inc(v_quotContext_4032_);
v___x_4040_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4039_, v_currMacroScope_4033_);
v___x_4041_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__6);
v___x_4042_ = l_Lean_Meta_SolveByElim_mkAssumptionSet___lam__0(v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__7));
lean_inc(v_currMacroScope_4033_);
lean_inc(v_quotContext_4032_);
v___x_4045_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4044_, v_currMacroScope_4033_);
v___x_4046_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__9);
v_sz_4047_ = lean_array_size(v_use_3979_);
v___x_4048_ = ((size_t)0ULL);
v___x_4049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4047_, v___x_4048_, v_use_3979_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; uint8_t v___x_4075_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref(v___x_4049_);
v___x_4051_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__10));
lean_inc(v_currMacroScope_4033_);
lean_inc(v_quotContext_4032_);
v___x_4052_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4051_, v_currMacroScope_4033_);
v___x_4053_ = lean_obj_once(&l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12, &l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12_once, _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__12);
v___x_4054_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__13));
lean_inc(v_currMacroScope_4033_);
lean_inc(v_quotContext_4032_);
v___x_4055_ = l_Lean_addMacroScope(v_quotContext_4032_, v___x_4054_, v_currMacroScope_4033_);
v___x_4056_ = 0;
v___x_4057_ = l_Lean_SourceInfo_fromRef(v_ref_4031_, v___x_4056_);
v___x_4058_ = lean_box(0);
v___x_4059_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__15));
v___x_4060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4057_);
lean_ctor_set(v___x_4060_, 1, v___x_4036_);
lean_ctor_set(v___x_4060_, 2, v___x_4040_);
lean_ctor_set(v___x_4060_, 3, v___x_4059_);
v___x_4061_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__17));
v___x_4062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4062_, 0, v_a_4035_);
lean_ctor_set(v___x_4062_, 1, v___x_4041_);
lean_ctor_set(v___x_4062_, 2, v___x_4045_);
lean_ctor_set(v___x_4062_, 3, v___x_4061_);
v___x_4063_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__19));
v___x_4064_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4064_, 0, v_a_4038_);
lean_ctor_set(v___x_4064_, 1, v___x_4046_);
lean_ctor_set(v___x_4064_, 2, v___x_4052_);
lean_ctor_set(v___x_4064_, 3, v___x_4063_);
v___x_4065_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__21));
v___x_4066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4066_, 0, v_a_4043_);
lean_ctor_set(v___x_4066_, 1, v___x_4053_);
lean_ctor_set(v___x_4066_, 2, v___x_4055_);
lean_ctor_set(v___x_4066_, 3, v___x_4065_);
v___x_4067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
lean_ctor_set(v___x_4067_, 1, v___x_4058_);
v___x_4068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4064_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4062_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4060_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_List_mapTR_loop___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__3(v___x_4070_, v___x_4058_);
v___x_4072_ = lean_unsigned_to_nat(0u);
v___x_4073_ = ((lean_object*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__22));
v___x_4074_ = lean_array_get_size(v_a_4050_);
v___x_4075_ = lean_nat_dec_lt(v___x_4072_, v___x_4074_);
if (v___x_4075_ == 0)
{
lean_dec(v_a_4050_);
v___y_4012_ = v___y_4029_;
v___y_4013_ = v___y_4030_;
v___y_4014_ = v___x_4058_;
v___y_4015_ = v___y_4027_;
v___y_4016_ = v___y_4028_;
v___y_4017_ = v___x_4071_;
v___y_4018_ = v___x_4073_;
goto v___jp_4011_;
}
else
{
uint8_t v___x_4076_; 
v___x_4076_ = lean_nat_dec_le(v___x_4074_, v___x_4074_);
if (v___x_4076_ == 0)
{
if (v___x_4075_ == 0)
{
lean_dec(v_a_4050_);
v___y_4012_ = v___y_4029_;
v___y_4013_ = v___y_4030_;
v___y_4014_ = v___x_4058_;
v___y_4015_ = v___y_4027_;
v___y_4016_ = v___y_4028_;
v___y_4017_ = v___x_4071_;
v___y_4018_ = v___x_4073_;
goto v___jp_4011_;
}
else
{
size_t v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_usize_of_nat(v___x_4074_);
v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4050_, v___x_4048_, v___x_4077_, v___x_4073_);
lean_dec(v_a_4050_);
v___y_4012_ = v___y_4029_;
v___y_4013_ = v___y_4030_;
v___y_4014_ = v___x_4058_;
v___y_4015_ = v___y_4027_;
v___y_4016_ = v___y_4028_;
v___y_4017_ = v___x_4071_;
v___y_4018_ = v___x_4078_;
goto v___jp_4011_;
}
}
else
{
size_t v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_usize_of_nat(v___x_4074_);
v___x_4080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__5(v_a_4050_, v___x_4048_, v___x_4079_, v___x_4073_);
lean_dec(v_a_4050_);
v___y_4012_ = v___y_4029_;
v___y_4013_ = v___y_4030_;
v___y_4014_ = v___x_4058_;
v___y_4015_ = v___y_4027_;
v___y_4016_ = v___y_4028_;
v___y_4017_ = v___x_4071_;
v___y_4018_ = v___x_4080_;
goto v___jp_4011_;
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v___x_4045_);
lean_dec(v_a_4043_);
lean_dec(v___x_4040_);
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v___y_4029_);
lean_dec_ref(v___f_4010_);
lean_dec(v_remove_3978_);
lean_dec(v_add_3977_);
v_a_4081_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4049_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4049_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* v_noDefaults_4099_, lean_object* v_star_4100_, lean_object* v_add_4101_, lean_object* v_remove_4102_, lean_object* v_use_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
uint8_t v_noDefaults_boxed_4109_; uint8_t v_star_boxed_4110_; lean_object* v_res_4111_; 
v_noDefaults_boxed_4109_ = lean_unbox(v_noDefaults_4099_);
v_star_boxed_4110_ = lean_unbox(v_star_4100_);
v_res_4111_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v_noDefaults_boxed_4109_, v_star_boxed_4110_, v_add_4101_, v_remove_4102_, v_use_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(size_t v_sz_4112_, size_t v_i_4113_, lean_object* v_bs_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___redArg(v_sz_4112_, v_i_4113_, v_bs_4114_, v___y_4117_, v___y_4118_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0___boxed(lean_object* v_sz_4121_, lean_object* v_i_4122_, lean_object* v_bs_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
size_t v_sz_boxed_4129_; size_t v_i_boxed_4130_; lean_object* v_res_4131_; 
v_sz_boxed_4129_ = lean_unbox_usize(v_sz_4121_);
lean_dec(v_sz_4121_);
v_i_boxed_4130_ = lean_unbox_usize(v_i_4122_);
lean_dec(v_i_4122_);
v_res_4131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_SolveByElim_mkAssumptionSet_spec__0(v_sz_boxed_4129_, v_i_boxed_4130_, v_bs_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4131_;
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
